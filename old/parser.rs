use pest::iterators::Pair;
use crate::lang::{CExpr, CSc, CAlter, Int, CData};
use string_interner::{DefaultStringInterner, Sym};
use std::num::ParseIntError;
use std::fmt::{Display, Formatter};

#[derive(Parser)]
#[grammar = "../pest/core.pest"]
struct CoreParser;

#[derive(Debug, Clone)]
pub struct Definitions {
    pub scs: Vec<CSc>,
    pub cons: Vec<CData>,
}

impl PartialEq for Definitions {
    fn eq(&self, other: &Self) -> bool {
        self.scs.len() == other.scs.len()
            && self.cons.len() == other.cons.len()
            && self.scs.iter().all(|x| other.scs.contains(x))
            && self.cons.iter().all(|x| other.cons.contains(x))
    }
}

pub fn parse_core_str<'s>(s: &'s str, interner: &mut DefaultStringInterner) -> Result<Definitions, Error<'s>> {
    use pest::Parser;
    let mut core = CoreParser::parse(Rule::program, s).map_err(|e| Error::Pest(e))?;
    //println!("{:#?}", &core);
    let mut defs = vec![];
    let mut cons= vec![];
    for sc in core.next().unwrap().into_inner() {
        match sc.as_rule() {
            Rule::sc => defs.push(parse_sc(sc, interner)?),
            Rule::cons => cons.push(parse_data(sc, interner)?),
            Rule::EOI => (),
            _other => return Err(Error::Pair(sc, "parse_core_str".to_string())),
        }
    }
    Ok(Definitions { scs: defs, cons })
}

fn parse_expr<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<CExpr, Error<'s>> {
    //println!("{:#?}", &pair);
    match pair.as_rule() {
        Rule::fexpr => {
            let mut iter = pair.into_inner();
            let res = iter.try_fold(None, |acc, p| {
                match acc {
                    None => Ok(Some(parse_expr(p, inter)?)),
                    Some(left) => Ok(Some(CExpr::App(Box::new(left), Box::new(parse_expr(p, inter)?)))),
                }
            })?.unwrap();
            Ok(res)
        },
        Rule::expr => parse_expr(pair.into_inner().next().unwrap(), inter),
        Rule::cexpr => parse_expr(pair.into_inner().next().unwrap(), inter),
        Rule::obj => parse_expr(pair.into_inner().next().unwrap(), inter),
        Rule::lete | Rule::letrec => {
            let rec = pair.as_rule() == Rule::letrec;
            let mut iter = pair.into_inner();
            let defs_iter = iter.next().unwrap().into_inner();

            let mut defs = vec![];

            for p in defs_iter {
                let mut iter = p.into_inner();
                let name = inter.get_or_intern(iter.next().unwrap().as_str());
                let expr = parse_expr(iter.next().unwrap(), inter)?;
                defs.push((name, expr));
            }

            let mut expr_iter = iter.next().unwrap().into_inner();
            let expr = parse_expr(expr_iter.next().unwrap(), inter)?;

            Ok(CExpr::Let {
                rec,
                defs,
                expr: Box::new(expr),
            })
        },
        Rule::case => {
            let mut iter = pair.into_inner();
            let expr = parse_expr(iter.next().unwrap(), inter)?;
            let alts_iter = iter.next().unwrap().into_inner();

            let mut alts = vec![];
            for p in alts_iter {
                let mut iter = p.into_inner();
                let cname = inter.get_or_intern(iter.next().unwrap().as_str());
                let vars = parse_maybe_vars(iter.next().unwrap(), inter)?;
                let expr = parse_expr(iter.next().unwrap(), inter)?;
                alts.push(CAlter::new(CData::new(cname, vars), expr))
            }
            Ok(CExpr::Case(Box::new(expr), alts))
        },
        Rule::lambda => {
            let mut iter = pair.into_inner();
            let vars = parse_maybe_vars(iter.next().unwrap(), inter)?;
            let expr = parse_expr(iter.next().unwrap(), inter)?;
            Ok(CExpr::Lambda(vars, Box::new(expr)))
        },
        Rule::num => match pair.as_str().parse::<Int>() {
                Ok(x) => Ok(CExpr::Num(x)),
                Err(e) => Err(Error::ParseInt(e)),
        },
        Rule::cname => Ok(CExpr::Constructor(inter.get_or_intern(pair.as_str()))),
        Rule::var => Ok(CExpr::Var(inter.get_or_intern(pair.as_str()))),
        _other => Err(Error::Pair(pair, "parse_expr failed".to_string())),
    }
}

fn parse_maybe_vars<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<Vec<Sym>, Error<'s>> {
    match pair.as_rule() {
        Rule::maybe_vars => match pair.into_inner().next() {
            Some(p) => parse_vars(p, inter),
            None => Ok(vec![]),
        }
        Rule::vars => parse_vars(pair, inter),
        _other => Err(Error::Pair(pair, "parse_maybe_vars failed".to_string())),
    }
}

fn parse_vars<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<Vec<Sym>, Error<'s>> {
    match pair.as_rule() {
        Rule::vars => {
            Ok(pair.into_inner().map(|p| {
                //println!("[{}]", p.as_str());
                inter.get_or_intern(p.as_str())
            }).collect::<Vec<_>>())
        }
        _other => Err(Error::Pair(pair, "parse_vars failed".to_string())),
    }
}

fn parse_sc<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<CSc, Error<'s>> {
    match pair.as_rule() {
        Rule::sc => {
            let mut iter = pair.into_inner();
            let name_str = iter.next().unwrap().as_str();
            //println!("({})", name_str);
            let name = inter.get_or_intern(name_str);
            let vars = iter.next().unwrap();
            let params = parse_maybe_vars(vars, inter)?;
            let expr = parse_expr(iter.next().unwrap(), inter)?;
            Ok(CSc::new(name, params, expr))
        },
        _other => Err(Error::Pair(pair, "parse_sc failed".to_string())),
    }
}

fn parse_data<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<CData, Error<'s>> {
    let mut iter = pair.into_inner();
    let cname = inter.get_or_intern(iter.next().unwrap().as_str());
    let vars = parse_maybe_vars(iter.next().unwrap(), inter)?;
    Ok(CData::new(cname, vars))
}

#[derive(Clone, Debug)]
pub enum Error<'s> {
    Pair(Pair<'s, Rule>, String),
    Pest(pest::error::Error<Rule>),
    ParseInt(ParseIntError),
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Pair(_, _) | Error::ParseInt(_) => write!(f, "{:?}", self),
            Error::Pest(p) => write!(f, "{}", p),
        }
    }
}
