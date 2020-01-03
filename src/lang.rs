use string_interner::Sym;

pub type Int = i64;

pub type CExpr = Expr<Sym, Sym>;
pub type CSc = Sc<Sym, Sym>;

#[derive(Debug, Clone)]
pub struct Sc<N, M> {
    name: N,
    params: Vec<N>,
    expr: Expr<N, M>,
}

impl<N, M> Sc<N, M> {
    pub fn new(name: N, params: Vec<N>, expr: Expr<N, M>) -> Self {
        Self { name, params, expr }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<N, M> {
    Var(N),
    Num(Int),
    Constructor(M),
    App(Box<Expr<N, M>>, Box<Expr<N, M>>),
    Let {
        rec: bool,
        defs: Vec<(N, Expr<N, M>)>,
        expr: Box<Expr<N, M>>,
    },
    Case(Box<Expr<N, M>>, Vec<Alter<N, M>>),
    Lambda(Vec<N>, Box<Expr<N, M>>),
}

#[derive(Debug, Clone)]
pub struct Alter<N, M> {
    cons: M,
    vars: Vec<N>,
    expr: Expr<N, M>,
}

impl<N, M> Alter<N, M> {
    pub fn new(cons: M, vars: Vec<N>, expr: Expr<N, M>) -> Self {
        Self { cons, vars, expr }
    }
}
