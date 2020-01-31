#![allow(dead_code)]

#[macro_use]
extern crate pest_derive;

use crate::parser::parse_core_str;
use string_interner::DefaultStringInterner;
use crate::lang::PrettyPrint;

mod lang;
mod parser;
//mod a_compiler;

fn main() {
    //test_0()
    reparse_test("core/test_0.core");
}

fn test_0() {
    let file = std::fs::read_to_string("core/test_0.core").unwrap();
    let mut interner = DefaultStringInterner::new();
    let defs = parse_core_str(&file, &mut interner);
    //println!("{:#?}", defs);
    println!("{:?}", interner.iter().collect::<Vec<_>>());
    match defs {
        Err(e) => println!("{:#?}", e),
        Ok(def) => {
            for e in def.scs {
                println!("{}", e.pretty_print_string(&interner).unwrap());

            }
            for c in def.cons {
                println!("{}", c.pretty_print_string(&interner).unwrap());
            }
        }
    }
}

fn reparse_test(filename: &str) {
    let file = std::fs::read_to_string(filename).unwrap();
    let mut interner = DefaultStringInterner::new();
    let defs = parse_core_str(&file, &mut interner);
    match defs {
        Err(e) => println!("{}", e),
        Ok(def) => {
            let mut copy = String::new();
            for e in def.scs.iter() {
                e.pretty_print(&mut copy, &interner).unwrap();
                copy.push('\n');
            }
            for e in def.cons.iter() {
                e.pretty_print(&mut copy, &interner).unwrap();
                copy.push('\n');
            }
            println!("{}", &copy);
            let mut interner2 = DefaultStringInterner::new();
            let defs2 = parse_core_str(&copy, &mut interner2);
            match defs2 {
                Err(e) => println!("{}", e),
                Ok(def2) => {
                    assert_eq!(def, def2);
                    dbg!(def);
                    dbg!(def2);
                }
            }
        }
    }
}
