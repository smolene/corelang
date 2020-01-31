use string_interner::{Sym, Symbol, StringInterner};
use std::fmt::{Write, Error};

pub type Int = i64;

pub type CExpr = Expr<Sym, Sym>;
pub type CSc = Sc<Sym, Sym>;
pub type CData = Data<Sym, Sym>;
pub type CAlter = Alter<Sym, Sym>;

#[derive(Debug, Clone, PartialEq)]
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

impl<S: Symbol + Clone> PrettyPrint for Sc<S, S> {
    type Symbol = S;

    fn pretty_print(&self, buf: &mut impl Write, inter: &StringInterner<S>) -> std::fmt::Result {
        write!(buf, "{} ", inter.resolve(self.name.clone()).unwrap())?;
        for p in self.params.iter() {
            write!(buf, "{} ", inter.resolve(p.clone()).unwrap())?;
        }
        write!(buf, "= ", )?;
        self.expr.pretty_print(buf, inter)?;
        write!(buf, ";")?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
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

impl<S: Symbol + Clone> PrettyPrint for Expr<S, S> {
    type Symbol = S;

    fn pretty_print(&self, buf: &mut impl Write, inter: &StringInterner<S>) -> std::fmt::Result {
        use Expr::*;
        match self {
            Var(n) => write!(buf, "{}", inter.resolve(n.clone()).unwrap())?,
            Num(x) => write!(buf, "{}", x)?,
            Constructor(name) => write!(buf, "{}", inter.resolve(name.clone()).unwrap())?,
            App(l, r) => {
                write!(buf, "(")?;
                l.pretty_print(buf, inter)?;
                write!(buf, " ")?;
                r.pretty_print(buf, inter)?;
                write!(buf, ")")?;
            },
            Let { rec, defs, expr } => {
                if *rec {
                    write!(buf, "letrec")?;
                } else {
                    write!(buf, "let")?;
                }
                for (n, e) in defs.iter() {
                    write!(buf, " {} = ", inter.resolve(n.clone()).unwrap())?;
                    e.pretty_print(buf, inter)?;
                }
                write!(buf, " in ")?;
                expr.pretty_print(buf, inter)?;
            }
            Case(e, v) => {
                write!(buf, "case ")?;
                e.pretty_print(buf, inter)?;
                write!(buf, " of")?;
                for alter in v {
                    write!(buf, " ")?;
                    alter.pretty_print(buf, inter)?;
                    write!(buf, ",")?;
                }
            },
            Lambda(vars, e) => {
                write!(buf, "\\")?;
                let mut iter = vars.iter();
                if let Some(first) = iter.next() {
                    write!(buf, "{}", inter.resolve(first.clone()).unwrap())?;
                    for v in iter {
                        write!(buf, " {}", inter.resolve(v.clone()).unwrap())?;
                    }
                }
                write!(buf, ". ")?;
                e.pretty_print(buf, inter)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Alter<N, M> {
    data: Data<N, M>,
    expr: Expr<N, M>,
}

impl<N, M> Alter<N, M> {
    pub fn new(data: Data<N, M>, expr: Expr<N, M>) -> Self {
        Self { data, expr }
    }
}

impl<S: Symbol + Clone> PrettyPrint for Alter<S, S> {
    type Symbol = S;

    fn pretty_print(&self, buf: &mut impl Write, inter: &StringInterner<Self::Symbol>) -> Result<(), Error> {
        self.data.pretty_print(buf, inter)?;
        write!(buf, " -> ")?;
        self.expr.pretty_print(buf, inter)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Data<N, M> {
    name: M,
    vars: Vec<N>,
}

impl<N, M> Data<N, M> {
    pub fn new(name: M, vars: Vec<N>) -> Self {
        Self { name, vars }
    }
}

impl<S: Symbol + Clone> PrettyPrint for Data<S, S> {
    type Symbol = S;

    fn pretty_print(&self, buf: &mut impl Write, inter: &StringInterner<Self::Symbol>) -> Result<(), Error> {
        write!(buf, "{}", inter.resolve(self.name.clone()).unwrap())?;
        for v in self.vars.iter() {
            write!(buf, " {}", inter.resolve(v.clone()).unwrap())?;
        }
        Ok(())
    }
}

pub trait PrettyPrint {
    type Symbol: Symbol;
    fn pretty_print(&self, buf: &mut impl Write, inter: &StringInterner<Self::Symbol>) -> std::fmt::Result;
    fn pretty_print_string(&self, inter: &StringInterner<Self::Symbol>) -> Result<String, std::fmt::Error> {
        let mut buf = String::new();
        self.pretty_print(&mut buf, inter)?;
        Ok(buf)
    }
}



