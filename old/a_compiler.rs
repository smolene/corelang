use std::rc::Rc;
use string_interner::Sym;

pub type Int = i64;
pub type RObject = Rc<Object>;
type RNode = Rc<Node>;

#[derive(Debug, Clone)]
pub enum Data {
    Object(RObject),
    Native(Int),
}

#[derive(Debug, Clone)]
pub struct Object {
    name: Sym,
    fields: Vec<Data>,
}

#[derive(Debug, Clone)]
pub struct Cons {
    name: Sym,
    num_of_fields: usize,
}

#[derive(Debug, Clone)]
pub enum Node {
    Data(Data),
    App(RNode, RNode),
    Sc(Sym),
    Cons(Cons),
    Rc(RNode),
}

#[derive(Debug, Clone)]
pub enum Inst {
    PushLocal(usize),
    PushSc(Sym),
    PushConst(Int),
    PushCons(Cons),
    MakeApp,
    Slide(usize),
    Unwind,
}

#[derive(Debug, Clone)]
pub struct Vm {
    inst: Vec<Inst>,
    data: Vec<Node>,
}

impl Vm {
    pub fn from_parts(inst: Vec<Inst>, data: Vec<Node>) -> Self {
        Self { inst, data }
    }

    pub fn step(&mut self, context: &mut ()) -> Result<bool, Error> {
        if let Some(instr) = self.inst.last() {

            match instr {
                Inst::PushLocal(n) => {
                    let node = self.data[self.data.len() - *n].clone();
                    self.data.push(node);
                },
                Inst::PushSc(sc) => {
                    let node = Node::Sc(sc.clone());
                    self.data.push(node);
                },
                Inst::PushConst(x) => {
                    let node = Node::Data(Data::Native(*x));
                    self.data.push(node);
                },
                Inst::PushCons(cons) => {
                    let mut vec = Vec::with_capacity(cons.num_of_fields);
                    for _ in 0..cons.num_of_fields {
                        let node = self.data.pop().ok_or_else(|| Error::NotEnoughStackArguments)?;
                        if let Node::Data(data) = &*node {
                            vec.push(data.clone());
                        }
                    }
                    self.data.push(Node::Data(Data::Object(Rc::new(Object { name: cons.name, fields: vec }))))
                },
                Inst::MakeApp => {
                    let f = self.data.pop().ok_or_else(|| Error::NotEnoughStackArguments)?;
                    let x = self.data.pop().ok_or_else(|| Error::NotEnoughStackArguments)?;
                    let node = Node::App(Rc::new(f), Rc::new(x));
                    self.data.push(node);
                },
                Inst::Slide(n) => {
                    let top = self.data.pop().ok_or_else(|| Error::NotEnoughStackArguments)?;
                    for _ in 0..*n {
                        self.data.pop()
                    }
                    self.data.push(top);
                },
                Inst::Unwind => {
                    
                },
                other => unimplemented!("{:?}", other),
            }

            Ok(false)
        } else {
            Ok(true)
        }
    }
}


pub enum Error {
    NotEnoughStackArguments,
}
