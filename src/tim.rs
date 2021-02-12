#![allow(dead_code)]

use crate::store::{Index, Store, GcStore, Handle};
use std::rc::Rc;
use std::fmt::Write;
use string_interner::{Sym, DefaultStringInterner};
use crate::parser::{Name, ScDef, CScDef, CExpr, Expr, parse_core_program, Program};
use std::collections::BTreeMap;
use std::time::Instant;
use std::io::{stdin, stdout, Write as IoWrite};
use nom::lib::std::collections::HashSet;

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
    Break,
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

    fn jump_to_code(ops: &mut Vec<Op>, code: &Code, _rec: &mut Vec<Code>) {
        ops.clear();
        ops.extend(code.0.iter().cloned().rev()); // rev because code stores 0: start, n-1: end but self.ops is a stack where n-1: start
        //rec.push(code.clone());
    }

    fn run(&mut self) -> Result<(), String> {
        let mut counter = 0;
        let mut res = Ok(false);
        loop {
            if res.is_err() || res == Ok(true) || counter == 0 {
                let mut buf = String::new();
                print!("{}> ", self.debug);
                stdout().flush().unwrap();
                stdin().read_line(&mut buf).unwrap();
                if buf.trim() == "run" {
                    counter = u64::max_value();
                } else if buf.starts_with("step") {
                    if let Some(s) = buf.split_whitespace().skip(1).next() {
                        if let Ok(n) = s.parse::<u64>() {
                            counter = n;
                        } else { continue; }
                    } else { continue; }
                } else if buf.trim() == "stack" {
                    for (i, Closure(idx, _)) in self.stack.iter().enumerate() {
                        if let Some(x) = self.code.lookup(*idx).1 {
                            println!("{}: {}", i, self.inter.resolve(x).unwrap());
                        }
                    }
                    continue;
                } else if buf.trim() == "graph" {
                    /*self.visit_reachable(|h, v, depth| {
                        println!("{:padding$}[{}]", "", h.get_inner(), padding = depth as usize * 2);
                        for Closure(i, _x) in v {
                            let name = self.code.lookup(*i).1
                                .and_then(|n| self.inter.resolve(n))
                                .unwrap_or("<unnamed>");

                            println!("{:padding$}| {}", "", name, padding = depth as usize * 2);
                        }
                    });*/
                    self.visit_reachable(|_h, v, depth, i| {
                        let name = self.code.lookup(v.0).1
                            .and_then(|n| self.inter.resolve(n))
                            .unwrap_or("<unnamed>");

                        println!("{:padding$}|{}: {}", "", i, name, padding = depth as usize * 2);
                    }, |h, _c, depth| {
                        println!("{:padding$}[{}]", "", h.get_inner(), padding = depth as usize * 2);
                    });
                } else if buf.trim() == "quit" {
                    return res.map(|_| ());
                } else if buf.trim() == "stackv" {
                    for (idx, val) in self.vstack.iter().enumerate() {
                        println!("{}: {}", idx, val);
                    }
                } else {
                    if let Err(s) = &res {
                        println!("Error: {:?}", s);
                        continue;
                    }
                    let mut s = String::new();
                    display_op(self.ops.last().unwrap_or(&Op::Break), &self.code, &self.heap, &self.frame_ptr, &mut s, &self.inter).unwrap();
                    print!("{}< {}", self.debug, &s);
                    res = self.step();
                    println!(" | {:?}", res);
                    counter = counter.saturating_sub(1);
                }
            } else {
                res = self.step();
                counter = counter.saturating_sub(1);
            }
        }
    }

    fn step(&mut self) -> Result<bool, String> {
        self.debug += 1;
        if let Some(op) = self.ops.pop() {
            match op {
                Op::Break => return Err("Break!".to_string()),
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

    fn visit_reachable<
        F: FnMut(Handle<FrameK>, &Closure, u64, usize),
        G: FnMut(Handle<FrameK>, &[Closure], u64),
    >(&self, mut f: F, mut g: G) {

        /*fn visit_preorder<F: FnMut(Handle<FrameK>, &[Closure], u64)>(tim: &Tim, fptr: &FramePtr, depth: u64, f: &mut F) {
            match fptr {
                FramePtr::Frame(h) => {
                    let frame = tim.heap.lookup(*h);
                    f(*h, frame.0.as_slice(), depth);
                    for Closure(_idx, new_fptr) in &frame.0 {
                        visit_preorder(tim, new_fptr, depth + 1, f);
                    }
                }
                FramePtr::Const(_c) => (),
                FramePtr::None => (),
            }
        }*/

        fn visit<
            F: FnMut(Handle<FrameK>, &Closure, u64, usize),
            G: FnMut(Handle<FrameK>, &[Closure], u64),
        >(tim: &Tim, fptr: &FramePtr, depth: u64, f: &mut F, g: &mut G) {
            match fptr {
                FramePtr::Frame(h) => {
                    let frame = tim.heap.lookup(*h);
                    g(*h, frame.0.as_slice(), depth);
                    for (i, c) in frame.0.iter().enumerate() {
                        f(*h, c, depth, i);
                        visit(tim, &c.1, depth + 1, f, g);
                    }
                }
                FramePtr::Const(_c) => (),
                FramePtr::None => (),
            }
        }

        let mut roots = vec![];
        if let Ok(&h) = self.frame_ptr.as_frame() {
            roots.push(h);
        }
        roots.extend(self.stack.iter().flat_map(|Closure(_, fptr)| fptr.as_frame().ok()));

        for h in roots {
            visit(self, &FramePtr::Frame(h), 0, &mut f, &mut g);
        }
    }

    fn list_reachable(&self) -> Vec<Handle<FrameK>> {
        let mut v = vec![];
        self.visit_reachable(|h, _f, _, _| v.push(h), |_, _, _| {});
        v
    }
}

fn make_tim_program(prog: &Program<Name>, mut inter: DefaultStringInterner) -> Tim {
    let (s, m, b) = compile_program(prog, &mut inter);
    Tim::new(s, m, b, inter)
}

fn predef(store: &mut Store<Code, CodeK>, inter: &mut DefaultStringInterner) -> BTreeMap<Name, Index<CodeK>> {
    let empty = inter.get_or_intern("__empty");
    let empty_idx = store.insert(Code(vec![], Some(empty)));
    let int_op = inter.get_or_intern("__int_op");
    let int_op_idx = store.insert(Code(vec![Op::PushV(VMode::FromFramePtr), Op::Return], Some(int_op)));
    let error = inter.get_or_intern("error");
    let error_idx = store.insert(Code(vec![Op::Break], Some(error)));

    let if_op = inter.get_or_intern("if");
    let if_op_x = inter.get_or_intern("__if_x");
    let if_op_t = inter.get_or_intern("__if_t");
    let if_op_f = inter.get_or_intern("__if_f");
    let if_t = store.insert(Code(vec![Op::Enter(Mode::Arg(1))], Some(if_op_t)));
    let if_f = store.insert(Code(vec![Op::Enter(Mode::Arg(0))], Some(if_op_f)));
    let if_x = store.insert(Code(vec![Op::Cond(if_t, if_f)], Some(if_op_x)));
    let if_idx = store.insert(Code(vec![Op::Take(3), Op::Push(Mode::Label(if_x)), Op::Enter(Mode::Arg(2))], Some(if_op))); // FIXME? it seems to work uwu

    macro_rules! def_op {
        ($name:ident, $bop:ident) => {
            {
                let n = inter.get_or_intern(stringify!($name));
                let n_1 = inter.get_or_intern(stringify!($name).to_string() + "_1");
                let n_2 = inter.get_or_intern(stringify!($name).to_string() + "_2");
                let n_idx_2 = store.insert(Code(vec![Op::BinOp(BinOp::$bop), Op::Return], Some(n_2)));
                let n_idx_1 = store.insert(Code(vec![Op::Push(Mode::Label(n_idx_2)), Op::Enter(Mode::Arg(1))], Some(n_1)));
                let n_idx = store.insert(Code(vec![Op::Take(2), Op::Push(Mode::Label(n_idx_1)), Op::Enter(Mode::Arg(0))], Some(n)));
                [(n, n_idx), (n_1, n_idx_1), (n_2, n_idx_2)]
            }
        };
    }

    macro_rules! def_many {
        ($($name:ident, $bop:ident),*) => {
            {
                let mut map = BTreeMap::<Name, Index<CodeK>>::new();
                $(
                    map.extend(def_op!($name, $bop).iter().copied());
                )*
                map
            }
        };
    }

    let mut map = def_many!(add, Add, sub, Sub, mul, Mul, div, Div, lt, Lt, lte, Lte, gt, Gt, gte, Gte, eq, Eq, neq, Neq);
    map.insert(empty, empty_idx);
    map.insert(int_op, int_op_idx);
    map.insert(error, error_idx);
    map.insert(if_op, if_idx);
    map.insert(if_op_t, if_t);
    map.insert(if_op_f, if_f);
    map.insert(if_op_x, if_x);
    map
}

fn compile_program(prog: &Program<Name>, inter: &mut DefaultStringInterner) -> (Store<Code, CodeK>, Index<CodeK>, BTreeMap<Name, Index<CodeK>>) {
    let mut store = Store::new();
    let pred = predef(&mut store, inter);
    let mut env = pred.iter().map(|(k, v)| (*k, Mode::Label(*v))).collect::<BTreeMap<Name, Mode>>();
    for ScDef(name, _args, _e) in prog.0.iter() {
        assert!(!env.contains_key(name));
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

    (store, main_idx.expect("No main supercombinator was declared"), pred)
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

fn display_all_code(store: &Store<Code, CodeK>, heap: &GcStore<Frame, FrameK>, frame_ptr: &FramePtr, w: &mut impl Write, inter: &DefaultStringInterner) -> std::fmt::Result {
    for c in store.inner().iter() {
        display_code(c, store, heap, frame_ptr, w, inter)?;
        write!(w, "\n")?;
    }
    Ok(())
}

fn display_code(c: &Code, store: &Store<Code, CodeK>, heap: &GcStore<Frame, FrameK>, frame_ptr: &FramePtr, w: &mut impl Write, inter: &DefaultStringInterner) -> std::fmt::Result {
    write!(w, "{}:\n", c.1.and_then(|n| inter.resolve(n)).unwrap_or("<unnamed>"))?;
    for (i, op) in c.0.iter().enumerate() {
        write!(w, "{:>3}: ", i)?;
        display_op(op, store, heap, frame_ptr, w, inter)?;
    }
    Ok(())
}

fn display_op(op: &Op, store: &Store<Code, CodeK>, heap: &GcStore<Frame, FrameK>, frame_ptr: &FramePtr, w: &mut impl Write, inter: &DefaultStringInterner) -> std::fmt::Result {
    write!(w, "{:?}", op)?;
    let mut f = |m: &Mode| match m {
        Mode::Label(i) => {
            if let Some(x) = store.lookup(*i).1 {
                write!(w, " --> {}", inter.resolve(x).unwrap())
            } else {
                Ok(())
            }
        },
        Mode::Arg(n) => {
            if let Ok(&fr) = frame_ptr.as_frame() {
                let frame = heap.lookup(fr);
                if let Some(Closure(index, _ptr)) = frame.0.get(*n) {
                    if let Some(x) = store.lookup(*index).1 {
                        write!(w, " --> {}", inter.resolve(x).unwrap())?
                    }
                }
            }
            Ok(())
        }
        _ => Ok(()),
    };
    match op {
        Op::Enter(m) => f(m)?,
        Op::Push(m) => f(m)?,
        Op::Cond(i, j) => {
            if let Some(x) = store.lookup(*i).1 {
                write!(w, " <l> --> {}", inter.resolve(x).unwrap())?;
            }
            if let Some(x) = store.lookup(*j).1 {
                write!(w, " <r> --> {}", inter.resolve(x).unwrap())?;
            }
        }
        _ => (),
    }
    write!(w, "\n")
}

pub fn test_file(path: &str) {
    let file = std::fs::read_to_string(path).unwrap();
    let parsed = parse_core_program(&file);
    let (prog, inter) = parsed.as_interned();

    println!("{}", prog.pretty_print_string(&inter));

    let mut tim = make_tim_program(&prog, inter);

    let mut s = String::new();
    display_all_code(&tim.code, &tim.heap, &tim.frame_ptr, &mut s, &mut tim.inter).unwrap();
    println!("{}", s);

    let now = Instant::now();
    let res = tim.run();
    let delta = now.elapsed();
    s.clear();
    display_code(&Code(tim.ops.clone(), None), &tim.code, &tim.heap, &tim.frame_ptr, &mut s, &tim.inter).unwrap();
    println!("{}", s);
    for code in tim.opsrecord.iter().skip(tim.opsrecord.len().saturating_sub(40)) {
        s.clear();
        display_code(code, &tim.code, &tim.heap, &tim.frame_ptr, &mut s, &tim.inter).unwrap();
        println!("{}", s);
    }
    let bytes = 0; //tim.heap.inner().len() * size_of::<Frame>();
    println!("finished: \n{:?}\nframe_ptr: {:?}\ndebug: {}\nused mem: {}B | {} objects\ntime: {}", res, tim.frame_ptr, tim.debug, bytes, tim.heap.inner().len(), delta.as_secs_f32());
    println!("{:?}", tim.vstack);
}
