#![allow(dead_code)]

use string_interner::{Sym, DefaultStringInterner};
use std::fmt::{Write, Debug};
use std::fmt;
use crate::parser::inner::whole_program;
use nom::error::VerboseError;

type BExpr<N> = Box<Expr<N>>;
pub type CExpr = Expr<Name>;
pub type Name = Sym;
pub type Alter<N> = (N, Vec<N>, Expr<N>);
pub type CProgram = Program<Name>;
pub type CScDef = ScDef<Name>;

pub fn parse_core_program(s: &str) -> Program<&'_ str> {

    fn convert(e: nom::Err<VerboseError<&str>>) -> VerboseError<&str> {
        match e {
            nom::Err::Incomplete(_) => unimplemented!(),
            nom::Err::Error(e) => e,
            nom::Err::Failure(e) => e,
        }
    }

    match whole_program(s) {
        Err(e) => panic!("{}", nom::error::convert_error(&s, convert(e))),
        Ok((_s, p)) => p,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program<N>(pub Vec<ScDef<N>>, pub Vec<Constructor<N>>);

impl<N> Program<N> {
    pub fn map<M>(&self, f: &mut impl FnMut(&N) -> M) -> Program<M> {
        Program(self.0.iter().map(|sc| sc.map(f)).collect(), self.1.iter().map(|cons| cons.map(f)).collect())
    }

    pub fn check_eq(&self, other: &Program<N>)
    where N: PartialEq + Debug {
        for (r, s) in self.0.iter().zip(other.0.iter()) {
            assert_eq!(r, s);
        }
        for (r, s) in self.1.iter().zip(other.1.iter()) {
            assert_eq!(r, s);
        }
        assert_eq!(self.0.len(), other.0.len());
        assert_eq!(self.1.len(), other.1.len());
    }
}

impl Program<&str> {
    pub fn as_interned(&self) -> (Program<Sym>, DefaultStringInterner) {
        let mut interner = DefaultStringInterner::new();
        (self.map(&mut |s: &&str| interner.get_or_intern(*s)), interner)
    }
}

impl Program<Sym> {
    pub fn pretty_print_string(&self, inter: &DefaultStringInterner) -> String {
        let mut s = String::new();
        self.pretty_print(&mut s, inter).unwrap();
        s
    }

    pub fn pretty_print(&self, f: &mut impl Write, inter: &DefaultStringInterner) -> fmt::Result {
        for c in &self.1 {
            c.pretty_print(f, inter)?;
            write!(f, "\n\n")?;
        }
        for s in &self.0 {
            s.pretty_print(f, inter)?;
            write!(f, "\n\n")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constructor<N>(N, usize);

impl<N> Constructor<N> {
    pub fn map<M>(&self, f: &mut impl FnMut(&N) -> M) -> Constructor<M> {
        Constructor(f(&self.0), self.1)
    }
}

impl Constructor<Sym> {
    pub fn pretty_print(&self, f: &mut impl Write, inter: &DefaultStringInterner) -> fmt::Result {
        write!(f, "data {}", inter.resolve(self.0).unwrap())?;
        for _ in 0..self.1 {
            write!(f, " x")?;
        }
        write!(f, ";")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ScDef<N>(pub N, pub Vec<N>, pub Expr<N>);

impl<N> ScDef<N> {
    pub fn map<M>(&self, mut f: &mut impl FnMut(&N) -> M) -> ScDef<M> {
        let ScDef(name, args, body) = self;
        ScDef(f(name), args.iter().map(&mut f).collect(), body.map(f))
    }
}

impl ScDef<Sym> {
    pub fn pretty_print(&self, f: &mut impl Write, inter: &DefaultStringInterner) -> fmt::Result {
        write!(f, "{} ", inter.resolve(self.0).unwrap())?;
        for s in &self.1 {
            write!(f, "{} ", inter.resolve(*s).unwrap())?;
        }
        write!(f, "= ")?;
        self.2.pretty_print(f, inter, 0)?;
        write!(f, ";")?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr<N> {
    Var(N),
    Num(i64),
    App(BExpr<N>, BExpr<N>),
    Let(bool, Vec<(N, Expr<N>)>, BExpr<N>),
    Case(BExpr<N>, Vec<Alter<N>>),
    Lambda(Vec<N>, BExpr<N>)
}

const INDENT: u32 = 4;

impl<N> Expr<N> {
    pub fn map<M>(&self, mut f: &mut impl FnMut(&N) -> M) -> Expr<M> {
        match self {
            Expr::Var(s) => Expr::Var(f(s)),
            Expr::Num(x) => Expr::Num(*x),
            Expr::App(l, r) => Expr::App(Box::new(l.map(f)), Box::new(r.map(f))),
            Expr::Let(rec, defs, e) => Expr::Let(*rec, defs.iter().map(|(s, e)| (f(s), e.map(f))).collect(), Box::new(e.map(f))),
            Expr::Case(e, alter) => Expr::Case(Box::new(e.map(f)), alter.iter().map(|(s, vs, es)| (f(s), vs.iter().map(&mut f).collect(), es.map(f))).collect()),
            Expr::Lambda(params, e) => Expr::Lambda(params.iter().map(&mut f).collect(), Box::new(e.map(f))),
        }
    }

    pub fn is_atomic(&self) -> bool {
        match self {
            Expr::Var(_) | Expr::Num(_) => true,
            _ => false,
        }
    }

    pub fn is_atomic_app(&self) -> bool {
        match self {
            Expr::Var(_) | Expr::Num(_) | Expr::App(_, _) => true,
            _ => false,
        }
    }
}

impl Expr<Sym> {
    pub fn pretty_print(&self, f: &mut impl Write, inter: &DefaultStringInterner, idt: u32) -> fmt::Result {
        fn indent(f: &mut impl Write, indent: u32) -> fmt::Result {
            for _ in 0..indent * INDENT {
                f.write_char(' ')?;
            }
            Ok(())
        }

        match self {
            Expr::Var(s) => write!(f, "{}", inter.resolve(*s).unwrap())?,
            Expr::Num(x) => write!(f, "{}", x)?,
            Expr::App(l, r) => {
                if l.is_atomic_app() {
                    l.pretty_print(f, inter, idt)?;
                } else {
                    write!(f, "(")?;
                    l.pretty_print(f, inter, idt)?;
                    write!(f, ")")?;
                }
                write!(f, " ")?;
                if r.is_atomic() {
                    r.pretty_print(f, inter, idt)?;
                } else {
                    write!(f, "(")?;
                    r.pretty_print(f, inter, idt)?;
                    write!(f, ")")?;
                }
            },
            Expr::Let(rec , defs, e) => {
                if *rec {
                    write!(f, "letrec ")?;
                } else {
                    write!(f, "let ")?;
                }
                for (i, (s, d)) in defs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "\n")?;
                    indent(f, idt + 1)?;
                    write!(f, "{} = ", inter.resolve(*s).unwrap())?;
                    d.pretty_print(f, inter, idt + 1)?;
                }
                write!(f, " \n")?;
                indent(f, idt + 1)?;
                write!(f, "in ")?;
                e.pretty_print(f, inter, idt + 1)?;
            },
            Expr::Case(e, a) => {
                write!(f, "case ")?;
                e.pretty_print(f, inter, idt)?;
                write!(f, " of")?;
                for (i, (s, v, e)) in a.iter().enumerate() {
                    if i != 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "\n")?;
                    indent(f, idt + 1)?;
                    write!(f, "| {} ", inter.resolve(*s).unwrap())?;
                    for s in v {
                        write!(f, "{} ", inter.resolve(*s).unwrap())?;
                    }
                    write!(f, "-> ")?;
                    e.pretty_print(f, inter, idt + 1)?;
                }
            },
            Expr::Lambda(v, e) => {
                write!(f, "\\")?;
                for (i, s) in v.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", inter.resolve(*s).unwrap())?;
                }
                write!(f, ". ")?;
                e.pretty_print(f, inter, idt + 1)?;
            },
        }
        Ok(())
    }
}

pub mod inner {
    use nom;
    use nom::error::{VerboseError, context};
    use nom::IResult;
    use nom::character::complete::{alpha1, multispace0, multispace1, digit1, space1};
    use string_interner::{DefaultStringInterner, Sym};
    use crate::parser::{ScDef, Expr, Program, Constructor};
    use nom::multi::{separated_list, many0, separated_nonempty_list, many1};
    use nom::bytes::complete::{tag, take_while};
    use nom::combinator::{map, not, complete, all_consuming, peek, verify, cut};
    use nom::sequence::{delimited, pair, preceded, terminated};
    use nom::branch::alt;

    const KEYWORDS: [&'static str; 6] = ["data", "case", "of", "let", "letrec", "in"];

    fn app_as_tree<N>(v: Vec<Expr<N>>) -> Expr<N> {
        let mut iter = v.into_iter();
        let mut top = iter.next().unwrap();
        for e in iter {
            top = Expr::App(Box::new(top), Box::new(e));
        }
        top
    }

    fn name_char(c: char) -> bool {
         c.is_alphabetic() || c == '_' //|| c == '-'
    }

    fn name(s: &str) -> IResult<&str, &str, VerboseError<&str>> {
        context("name", |s| {
            verify(take_while(name_char), |s: &&str| s.len() > 0 && !KEYWORDS.contains(s))(s)
        })(s)
    }

    pub fn whole_program(s: &str) -> IResult<&str, Program<&str>, VerboseError<&str>> {
        context("whole_program", |s| {
            all_consuming(cut(program))(s)
        })(s)
    }

    pub fn program(s: &str) -> IResult<&str, Program<&str>, VerboseError<&str>> {
        context("program", |s| {
            let (s, _) = multispace0(s)?;
            let (s, cons) = context("cons", many0(preceded(multispace0, constructor)))(s)?;
            let (s, _) = multispace0(s)?;
            let (s, sc) = context("scdef",
              many1(preceded(delimited(multispace0, many0(comment), multispace0), supercombinator))
            )(s)?;
            let (s, _) = multispace0(s)?;
            Ok((s, Program(sc, cons)))
        })(s)
    }

    pub fn comment(s: &str) -> IResult<&str, (), VerboseError<&str>> {
        context("comment", |s| {
            let (s, _) = tag("//")(s)?;
            let (s, _) = take_while(|c| c != '\n')(s)?;
            Ok((s, ()))
        })(s)
    }

    fn constructor(s: &str) -> IResult<&str, Constructor<&str>, VerboseError<&str>> {
        context("constructor", |s| {
            let (s, _) = tag("data")(s)?;
            let (s, _) = multispace1(s)?;
            //dbg!(s);
            cut(|s| {
                let (s, xs) = context("constructor_args", separated_nonempty_list(multispace1, name))(s)?;
                //dbg!(s);
                let (s, _) = preceded(multispace0, tag(";"))(s)?;
                //dbg!(s);
                Ok((s, Constructor(*xs.first().unwrap(), xs.len() - 1)))
            })(s)
        })(s)
    }

    fn supercombinator(s: &str) -> IResult<&str, ScDef<&str>, VerboseError<&str>> {
        context("supercombinator", |s| {
            let (s, n) = name(s)?;
            let (s, _) = multispace1(s)?;
            cut(move |s| {
                let (s, vars) = separated_list(multispace1, name)(s)?;
                let (s, _) = multispace0(s)?;
                let (s, _) = tag("=")(s)?;
                let (s, _) = multispace0(s)?;
                let (s, e) = expr(s)?;
                let (s, _) = multispace0(s)?;
                let (s, _) = tag(";")(s)?;
                Ok((s, ScDef(n, vars, e)))
            })(s)
        })(s)
    }

    fn expr(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("expr", alt((
            letdef,
            case,
            lambda,
            //context("many_list", map(separated_nonempty_list(multispace0, atomic_expr), app_as_tree)),
            context("many_list", map(many1(terminated(atomic_expr, multispace0)), app_as_tree)),
        )))(s)
    }

    fn atomic_expr(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("atomic_expr", alt((
            var,
            num,
            paren
        )))(s)
    }

    fn var(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("var", map(name, |s| {/*dbg!(s);*/ Expr::Var(s)}))(s)
    }

    fn num(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("num", map(digit1, |n: &str| {/*dbg!(&n);*/ Expr::Num(n.parse::<i64>().unwrap())}))(s)
    }

    fn paren(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("paren", delimited(pair(tag("("), multispace0), expr, pair(multispace0, tag(")"))))(s)
    }

    fn letdef(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("letdef", |s| {
            let (s, b) = map(alt((tag("let"), tag("letrec"))), |s| s == "letrec")(s)?;
            //dbg!(b);
            let (s, _) = multispace1(s)?;
            cut(move |s| {
                let (s, v) = separated_nonempty_list(delimited(multispace0, tag(","), multispace0), letdefinition)(s)?;
                //dbg!(&v);
                let (s, _) = multispace0(s)?;
                let (s, _) = tag("in")(s)?;
                let (s, _) = multispace0(s)?;
                let (s, e) = expr(s)?;
                Ok((s, Expr::Let(b, v, Box::new(e))))
            })(s)
        })(s)
    }

    fn letdefinition(s: &str) -> IResult<&str, (&str, Expr<&str>), VerboseError<&str>> {
        context("letdefinition", |s| {
            let (s, n) = name(s)?;
            let (s, _) = delimited(multispace0, tag("="), multispace0)(s)?;
            //dbg!("letdefinition_expr");
            let (s, e) = expr(s)?;
            Ok((s, (n, e)))
        })(s)
    }

    fn case(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("case", |s| {
            let (s, _) = tag("case")(s)?;
            let (s, _) = multispace1(s)?;
            //dbg!("tag_ok");
            cut(|s| {
                let (s, e) = context("case_expr", expr)(s)?;
                //dbg!("expr_ok");
                let (s, _) = multispace0(s)?;
                let (s, _) = tag("of")(s)?;
                //dbg!("of_ok");
                let (s, _) = multispace0(s)?;
                let (s, a) = separated_nonempty_list(delimited(multispace0, tag(","), multispace0), case_arm)(s)?;
                Ok((s, Expr::Case(Box::new(e), a)))
            })(s)
        })(s)
    }

    fn case_arm(s: &str) -> IResult<&str, (&str, Vec<&str>, Expr<&str>), VerboseError<&str>> {
        //dbg!("case_arm");
        context("case_arm", |s| {
            let (s, _) = tag("|")(s)?;
            //dbg!("bar_ok");
            let (s, _) = multispace0(s)?;
            cut(|s| {
                let (s, mut xs) = separated_nonempty_list(multispace1, name)(s)?;
                //dbg!("list_ok");
                let (s, _) = multispace0(s)?;
                let (s, _) = tag("->")(s)?;
                let (s, _) = multispace0(s)?;
                let (s, e) = expr(s)?;
                Ok((s, (xs.remove(0), xs, e)))
            })(s)
        })(s)
    }


    fn lambda(s: &str) -> IResult<&str, Expr<&str>, VerboseError<&str>> {
        context("lambda", |s| {
            let (s, _) = tag("\\")(s)?;
            let (s, _) = multispace0(s)?;
            cut(|s| {
                let (s, v) = separated_nonempty_list(multispace1, name)(s)?;
                let (s, _) = tag(".")(s)?;
                let (s, _) = multispace0(s)?;
                let (s, e) = expr(s)?;
                Ok((s, Expr::Lambda(v, Box::new(e))))
            })(s)
        })(s)
    }
}

