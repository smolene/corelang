#![allow(dead_code)]

#[macro_use]
extern crate pest_derive;

use crate::parser::parse_core_str;
use string_interner::DefaultStringInterner;
use crate::lang::PrettyPrint;

mod lang;
mod parser;

fn main() {
    test_0()
}

fn test_0() {
    let file = std::fs::read_to_string("core/test_0.core").unwrap();
    let mut interner = DefaultStringInterner::new();
    let defs = parse_core_str(&file, &mut interner);
    //println!("{:#?}", defs);
    println!("{:?}", interner.iter().collect::<Vec<_>>());
    match defs {
        Err(e) => println!("{:#?}", e),
        Ok(def) => for e in def.scs {
            println!("{}", e.pretty_print_string(&interner).unwrap());
        }
    }
}
