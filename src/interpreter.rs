#![allow(dead_code)]

use string_interner::Sym;
use std::collections::VecDeque;
use crate::store::{Index, Store, GcStore, Handle};

pub struct Scomb {
    name: Option<Sym>,
    opcodes: Vec<Opcode>,
}

pub enum Expr {
    App(Handle, Handle),
    Const(Const),
    Name(Index),
}

#[derive(Copy, Clone)]
pub enum Opcode {
    Unwind,
    PushArg(usize),
    PushConst(Const),
    PushName(Index),
    MakeApp,
    BinFn(fn(Handle, Handle, &mut GcStore<Expr>) -> Handle),
    Slide(usize),
}

#[derive(Debug, Copy, Clone)]
pub struct Const(i64);

pub struct GMachine {
    code: Vec<Opcode>,
    stack: VecDeque<Handle>,
    heap: GcStore<Expr>,
    scomb: Store<Scomb>,
}

impl GMachine {
    pub fn new(start: Index, scomb: Store<Scomb>) -> Self {
        let mut s = Self {
            code: Vec::new(),
            stack: VecDeque::new(),
            heap: GcStore::new(),
            scomb,
        };
        s.stack.push_back(s.heap.insert(Expr::Name(start)));
        s
    }

    pub fn step(&mut self) -> Result<bool, String> {
        if let Some(op) = self.code.pop() {
            match op {
                Opcode::PushConst(c) => {
                    let h = self.heap.insert(Expr::Const(c));
                    self.stack.push_back(h);
                },
                Opcode::PushName(index) => {
                    let h = self.heap.insert(Expr::Name(index));
                    self.stack.push_back(h);
                },
                Opcode::PushArg(n) => {
                    let h = *self.stack.get(self.stack.len() - 2 - n).ok_or_else(|| "stack not big enough in push arg".to_string())?;
                    self.stack.push_back(h);
                },
                Opcode::MakeApp => {
                    let h0 = self.stack.pop_back().ok_or_else(|| "stack too small in make app, 0".to_string())?;
                    let h1 = self.stack.pop_back().ok_or_else(|| "stack too small in make app, 1".to_string())?;
                    let app = self.heap.insert(Expr::App(h0, h1));
                    self.stack.push_back(app);
                },
                Opcode::BinFn(f) => {
                    let h0 = self.stack.pop_back().ok_or_else(|| "stack too small in make app, 0".to_string())?;
                    let h1 = self.stack.pop_back().ok_or_else(|| "stack too small in make app, 1".to_string())?;
                    let fx = f(h0, h1, &mut self.heap);
                    self.stack.push_back(fx);
                }
                Opcode::Slide(n) => drop(self.stack.drain(..n)),
                Opcode::Unwind => {
                    Err("unwind".to_string())?
                }
            }

            Ok(true)
        } else {
            // end
            Ok(false)
        }
    }

    pub fn run(&mut self) -> Result<(), String> {
        loop {
            match self.step() {
                Ok(x) => if !x {
                    return Ok(())
                },
                Err(e) => return Err(e),
            }
        }
    }
}

pub fn test_interpreter() {
    // f g x = K (g x)
    let fun = Scomb {
        name: None,
        opcodes: vec![],
    };
}

pub fn compile_scomb() {

}
