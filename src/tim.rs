#![allow(dead_code)]

use crate::store::{Index, Store, GcStore, Handle};
use std::rc::Rc;
use std::fmt::Write;
use string_interner::{Sym, DefaultStringInterner};
use crate::parser::{Name, ScDef, CScDef, CExpr, Expr, parse_core_program, Program};
use nom::lib::std::collections::BTreeMap;

#[derive(Copy, Clone, Debug)]
struct CodeK;

#[derive(Copy, Clone, Debug)]
struct FrameK;

#[derive(Clone, Debug)]
struct Code(Vec<Op>, Option<Name>);

#[derive(Clone, Debug)]
struct Closure(Index<CodeK>, FramePtr);

#[derive(Clone, Debug)]
struct Frame(Vec<Closure>);

#[derive(Clone, Debug)]
enum FramePtr {
    Frame(Handle<FrameK>),
    Const(Const),
    None,
}

impl FramePtr {
    fn as_frame(&self) -> Result<&Handle<FrameK>, String> {
        match self {
            FramePtr::Frame(h) => Ok(h),
            _other => Err(format!("Expected FramePtr::Frame but got {:?}", self)),
        }
    }
}

#[derive(Clone, Debug)]
enum Op {
    Take(usize),
    Push(Mode),
    Enter(Mode),
    Return,
    PushV(VMode),
    BinOp(BinOp),
    Cond(Index<CodeK>, Index<CodeK>),
}

#[derive(Clone, Debug)]
enum Mode {
    Arg(usize),
    Label(Index<CodeK>),
    Const(Const),
}

#[derive(Clone, Debug)]
enum VMode {
    FromFramePtr,
    Int(Int),
}

#[derive(Clone, Debug)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Lte,
    Gt,
    Gte,
    Eq,
    Neq,
}

type Int = i64;

#[derive(Clone, Debug)]
enum Const {
    Int(Int),
}

#[derive(Clone, Debug)]
struct Tim {
    ops: Vec<Op>,
    frame_ptr: FramePtr,
    stack: Vec<Closure>,
    vstack: Vec<Int>,
    heap: GcStore<Frame, FrameK>,
    code: Store<Code, CodeK>,
    main: Index<CodeK>,
    predef: BTreeMap<Name, Index<CodeK>>,
    inter: DefaultStringInterner,
    debug: usize,
    opsrecord: Vec<Code>,
}

impl Tim {
    fn new(code: Store<Code, CodeK>, main: Index<CodeK>, predef: BTreeMap<Name, Index<CodeK>>, mut inter: DefaultStringInterner) -> Self {
        let mut s = Self {
            ops: vec![],
            frame_ptr: FramePtr::None,
            stack: vec![Closure(*predef.get(&mut inter.get_or_intern("__empty")).unwrap(), FramePtr::None)],
            vstack: vec![],
            heap: GcStore::new(),
            code,
            main,
            predef,
            inter,
            debug: 0,
            opsrecord: vec![],
        };
        Self::jump_to_code(&mut s.ops, s.code.lookup(main), &mut s.opsrecord);
        s
    }

    fn jump_to_code(ops: &mut Vec<Op>, code: &Code, rec: &mut Vec<Code>) {
        ops.clear();
        ops.extend(code.0.iter().cloned().rev()); // rev because code stores 0: start, n-1: end but self.ops is a stack where n-1: start
        rec.push(code.clone());
    }

    fn run(&mut self) -> Result<(), String> {
        loop {
            match self.step() {
                Ok(true) => return Ok(()),
                Err(s) => return Err(s),
                _ => (),
            }
        }
    }

    fn step(&mut self) -> Result<bool, String> {
        self.debug += 1;
        if let Some(op) = self.ops.pop() {
            match op {
                Op::Take(n) => {
                    if self.stack.len() < n {
                        return Err("Not enough arguments on stack".to_string());
                    }
                    let frame = Frame(self.stack.drain(self.stack.len() - n..).collect());
                    let handle = self.heap.insert(frame);
                    self.frame_ptr = FramePtr::Frame(handle);
                }
                Op::Push(mode) => {
                    match mode {
                        Mode::Arg(n) => {
                            let frame = self.heap.lookup(*self.frame_ptr.as_frame()?);
                            let nth = frame.0.get(n).ok_or("Not enough closures in frame")?;
                            self.stack.push(nth.clone());
                        }
                        Mode::Label(index) => {
                            let closure = Closure(index, self.frame_ptr.clone());
                            self.stack.push(closure);
                        }
                        Mode::Const(x) => {
                            let closure = Closure(*self.predef.get(&self.inter.get_or_intern("__int_op")).unwrap(), FramePtr::Const(x));
                            self.stack.push(closure);
                        }
                    }
                }
                Op::Enter(mode) => {
                    match mode {
                        Mode::Arg(n) => {
                            let frame = self.heap.lookup(*self.frame_ptr.as_frame()?);
                            let Closure(index, ptr) = frame.0.get(n).ok_or("Not enough closures in frame")?;
                            let code = self.code.lookup(*index);
                            self.frame_ptr = ptr.clone();
                            Self::jump_to_code(&mut self.ops, code, &mut self.opsrecord);
                        }
                        Mode::Label(index) => {
                            let code = self.code.lookup(index);
                            Self::jump_to_code(&mut self.ops, code, &mut self.opsrecord);
                        }
                        Mode::Const(_x) => {
                            let code = self.code.lookup(*self.predef.get(&self.inter.get_or_intern("__int_op")).unwrap());
                            Self::jump_to_code(&mut self.ops, code, &mut self.opsrecord);
                        }
                    }
                }
                Op::Return => {
                    let Closure(idx, fptr) = self.stack.pop().ok_or("Not enough closures on stack")?;
                    let code = self.code.lookup(idx);
                    Self::jump_to_code(&mut self.ops, code, &mut self.opsrecord);
                    self.frame_ptr = fptr;
                }
                Op::PushV(mode) => {
                    match mode {
                        VMode::Int(n) => self.vstack.push(n),
                        VMode::FromFramePtr => self.vstack.push(match self.frame_ptr {
                            FramePtr::Const(Const::Int(n)) => n,
                            _ => return Err("Invalid frame pointer to push".to_string())
                        }),
                    }
                }
                Op::BinOp(bop) => {
                    let l = self.vstack.pop().ok_or("Not enough values on Vstack for binop l")?;
                    let r = self.vstack.pop().ok_or("Not enough values on Vstack for binop r")?;
                    use BinOp::*;
                    let res = match bop {
                        Add => l + r,
                        Sub => l - r,
                        Mul => l * r,
                        Div => l / r,
                        Lt => (l < r).into(),
                        Lte => (l <= r).into(),
                        Gt => (l > r).into(),
                        Gte => (l >= r).into(),
                        Eq => (l == r).into(),
                        Neq => (l != r).into(),
                    };
                    self.vstack.push(res);
                }
                Op::Cond(t, f) => {
                    let n = self.vstack.pop().ok_or("Not enough values on Vstack for cond")?;
                    let code = self.code.lookup(if n == 0 { f } else { t }); // 0 => false, !0 => true
                    Self::jump_to_code(&mut self.ops, code, &mut self.opsrecord);
                }
            }
            Ok(false)
        } else {
            Ok(true)
        }
    }
}

fn make_tim_program(prog: &Program<Name>, mut inter: DefaultStringInterner) -> Tim {
    let (s, m, b) = compile_program(prog, &mut inter);
    Tim::new(s, m, b, inter)
}

fn defaults(store: &mut Store<Code, CodeK>, inter: &mut DefaultStringInterner) -> BTreeMap<Name, Index<CodeK>> {
    let empty = inter.get_or_intern("__empty");
    let empty_idx = store.insert(Code(vec![], Some(empty)));
    let int_op = inter.get_or_intern("__int_op");
    let int_op_idx = store.insert(Code(vec![Op::PushV(VMode::FromFramePtr), Op::Return], Some(int_op)));

    let add = inter.get_or_intern("add");
    let add_idx = empty_idx;

    vec![(empty, empty_idx), (int_op, int_op_idx), (add, add_idx)].into_iter().collect()
}

fn compile_program(prog: &Program<Name>, inter: &mut DefaultStringInterner) -> (Store<Code, CodeK>, Index<CodeK>, BTreeMap<Name, Index<CodeK>>) {
    let mut store = Store::new();
    let mut env = BTreeMap::new();
    for ScDef(name, _args, _e) in prog.0.iter() {
        env.insert(*name, Mode::Label(store.insert(Code(vec![], Some(*name))))); // insert empty code sequences
    }
    let main = inter.get_or_intern("main");
    let mut main_idx = None;
    for sc in prog.0.iter() {
        let code = compile_sc(&mut env, sc, &mut store, inter);
        let index = env.get(&sc.0).unwrap();
        if let Mode::Label(idx) = index {
            *store.lookup_mut(*idx) = code;
            if sc.0 == main {
                main_idx = Some(*idx)
            }
        } else { unreachable!() }
    }

    let d = defaults(&mut store, inter);
    (store, main_idx.expect("No main supercombinator was declared"), d)
}

fn compile_sc(env: &BTreeMap<Name, Mode>, sc: &CScDef, store: &mut Store<Code, CodeK>, inter: &mut DefaultStringInterner) -> Code {
    let ScDef(name, args, body) = sc;
    let mut code = Code(vec![], Some(*name));
    for n in args.iter() {
        if env.contains_key(n) {
            panic!("Name already defined! (most probably a supercombinator name): {:?}", inter.resolve(*n));
        }
    }
    if args.len() > 0 {
        let mut new = env.clone();
        new.extend(args.iter().rev().enumerate().map(|(i, &n)| (n, Mode::Arg(i)))); // bad but cant do better rn

        compile_r(&new, body, &mut code, store, inter, sc.0);
    } else {
        compile_r(env, body, &mut code, store, inter, sc.0);
    };

    code.0.push(Op::Take(args.len()));
    code.0.reverse();
    code
}

fn compile_r(env: &BTreeMap<Name, Mode>, expr: &Expr<Name>, code: &mut Code, store: &mut Store<Code, CodeK>, inter: &mut DefaultStringInterner, sc_name: Name) {
    match expr {
        Expr::App(l, r) => {
            compile_r(env, l, code, store, inter, sc_name);
            let mode = compile_a(env, r, store, inter, sc_name);
            code.0.push(Op::Push(mode));
        }
        e @ Expr::Var(_) => {
            let mode = compile_a(env, e, store, inter, sc_name);
            code.0.push(Op::Enter(mode));
        }
        e @ Expr::Num(_) => {
            let mode = compile_a(env, e, store, inter, sc_name);
            code.0.push(Op::Enter(mode));
        }
        other => unimplemented!("compile_r: {:?}", other),
    }
}

fn compile_a(env: &BTreeMap<Name, Mode>, expr: &Expr<Name>, store: &mut Store<Code, CodeK>, inter: &mut DefaultStringInterner, sc_name: Name) -> Mode {
    match expr {
        Expr::Var(n) => env.get(n).unwrap_or_else(|| panic!("Could not find variable: {:?}", inter.resolve(*n))).clone(),
        Expr::Num(x) => Mode::Const(Const::Int(*x)),
        _ => {
            let mut buf = format!("{} --> ", inter.resolve(sc_name).unwrap());
            expr.pretty_print(&mut buf, inter, 0).unwrap();
            let mut code = Code(vec![], Some(inter.get_or_intern(buf)));
            compile_r(env, expr, &mut code, store, inter, sc_name);
            code.0.reverse();
            let index = store.insert(code);
            Mode::Label(index)
        },
    }
}

fn display_all_code(store: &Store<Code, CodeK>, w: &mut impl Write, inter: &DefaultStringInterner) -> std::fmt::Result {
    for c in store.inner().iter() {
        display_code(c, store, w, inter)?;
        write!(w, "\n")?;
    }
    Ok(())
}

fn display_code(c: &Code, store: &Store<Code, CodeK>, w: &mut impl Write, inter: &DefaultStringInterner) -> std::fmt::Result {
    write!(w, "{}:\n", c.1.and_then(|n| inter.resolve(n)).unwrap_or("<unnamed>"))?;
    for (i, op) in c.0.iter().enumerate() {
        write!(w, "{:>3}: {:?}", i, op)?;
        let mut f = |m: &Mode| match m {
            Mode::Label(i) => {
                if let Some(x) = store.lookup(*i).1 {
                    write!(w, " --> {}", inter.resolve(x).unwrap())
                } else {
                    Ok(())
                }
            },
            _ => Ok(()),
        };
        match op {
            Op::Enter(m) => f(m)?,
            Op::Push(m) => f(m)?,
            _ => (),
        }
        write!(w, "\n")?;
    }
    Ok(())
}

pub fn test_file(path: &str) {
    let file = std::fs::read_to_string(path).unwrap();
    let parsed = parse_core_program(&file);
    let (prog, inter) = parsed.as_interned();

    println!("{}", prog.pretty_print_string(&inter));

    let mut tim = make_tim_program(&prog, inter);

    let mut s = String::new();
    display_all_code(&tim.code, &mut s, &mut tim.inter).unwrap();
    println!("{}", s);

    let res = tim.run();
    s.clear();
    display_code(&Code(tim.ops.clone(), None), &tim.code, &mut s, &tim.inter).unwrap();
    println!("{}", s);
    for code in tim.opsrecord {
        s.clear();
        display_code(&code, &tim.code, &mut s, &tim.inter).unwrap();
        println!("{}", s);
    }
    println!("finished: \n{:?}\n{:?}\n{}", res, tim.frame_ptr, tim.debug);
    println!("{:?}", tim.vstack);
}
