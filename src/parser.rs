use pest::iterators::Pair;
use crate::lang::{CExpr, CSc, Alter, Int};
use string_interner::{DefaultStringInterner, Sym};
use std::num::ParseIntError;

#[derive(Parser)]
#[grammar = "../pest/core.pest"]
struct CoreParser;

#[derive(Debug, Clone)]
pub struct Definitions {
    scs: Vec<CExpr>,
}

pub fn parse_core_str<'s>(s: &'s str, interner: &mut DefaultStringInterner) -> Result<Definitions, Error<'s>> {
    use pest::Parser;
    let core = CoreParser::parse(Rule::program, s).map_err(|e| Error::Pest(e))?;
    let mut defs = Vec::with_capacity(core.size_hint().0);
    for sc in core {
        defs.push(parse_expr(sc, interner)?);
    }
    Ok(Definitions { scs: defs })
}

fn parse_expr<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<CExpr, Error<'s>> {
    println!("{:#?}", &pair);
    match pair.as_rule() {
        Rule::expr => {
            let mut iter = pair.into_inner();
            let first = iter.next().unwrap();
            match first.as_rule() {
                Rule::again => {
                    let again = first.into_inner().try_fold(None, |acc, p| {
                        match acc {
                            None => Ok(Some(parse_expr(p, inter)?)),
                            Some(left) => Ok(Some(CExpr::App(Box::new(left), Box::new(parse_expr(p, inter)?)))),
                        }
                    })?.unwrap();
                    let aexpr = iter.next().unwrap();
                    Ok(CExpr::App(Box::new(again), Box::new(parse_expr(aexpr, inter)?)))
                },
                Rule::bexpr => parse_expr(first, inter),
                _other => Err(Error::Pair(first))
            }
        },
        Rule::bexpr => parse_expr(pair.into_inner().next().unwrap(), inter),
        Rule::aexpr => parse_expr(pair.into_inner().next().unwrap(), inter),
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
                alts.push(Alter::new(cname, vars, expr))
            }
            Ok(CExpr::Case(Box::new(expr), alts))
        },
        Rule::lambda => {
            let mut iter = pair.into_inner();
            let vars = parse_vars(iter.next().unwrap(), inter)?;
            let expr = parse_expr(iter.next().unwrap(), inter)?;
            Ok(CExpr::Lambda(vars, Box::new(expr)))
        },
        Rule::num => match pair.as_str().parse::<Int>() {
                Ok(x) => Ok(CExpr::Num(x)),
                Err(e) => Err(Error::ParseInt(e)),
        },
        Rule::cname => Ok(CExpr::Constructor(inter.get_or_intern(pair.as_str()))),
        Rule::var => Ok(CExpr::Var(inter.get_or_intern(pair.as_str()))),
        _other => Err(Error::Pair(pair)),
    }
}

fn parse_maybe_vars<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<Vec<Sym>, Error<'s>> {
    match pair.as_rule() {
        Rule::maybe_vars => match pair.into_inner().next() {
            Some(p) => parse_vars(p, inter),
            None => Ok(vec![]),
        }
        Rule::vars => parse_vars(pair, inter),
        _other => Err(Error::Pair(pair)),
    }
}

fn parse_vars<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<Vec<Sym>, Error<'s>> {
    match pair.as_rule() {
        Rule::vars => {
            Ok(pair.into_inner().map(|p| inter.get_or_intern(p.as_str())).collect::<Vec<_>>())
        }
        _other => Err(Error::Pair(pair)),
    }
}

fn parse_sc<'s>(pair: Pair<'s, Rule>, inter: &mut DefaultStringInterner) -> Result<CSc, Error<'s>> {
    match pair.as_rule() {
        Rule::sc => {
            let mut iter = pair.into_inner();
            let mut vars = iter.next().unwrap().into_inner();
            let name = inter.get_or_intern(vars.next().unwrap().as_str());
            let params = vars.map(|p| inter.get_or_intern(p.as_str())).collect::<Vec<_>>();
            let expr = parse_expr(iter.next().unwrap(), inter)?;
            Ok(CSc::new(name, params, expr))
        },
        _other => Err(Error::Pair(pair)),
    }
}

#[derive(Clone, Debug)]
pub enum Error<'s> {
    Pair(Pair<'s, Rule>),
    Pest(pest::error::Error<Rule>),
    ParseInt(ParseIntError),
}
