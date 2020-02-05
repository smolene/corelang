#![allow(unused_imports)]

use crate::parser::inner::{program, whole_program};
use nom::error::VerboseError;
use string_interner::DefaultStringInterner;

mod parser;

fn main() {
    parse_test("core/test_0.core");
}

fn convert(e: nom::Err<VerboseError<&str>>) -> VerboseError<&str> {
    match e {
        nom::Err::Incomplete(_) => unimplemented!(),
        nom::Err::Error(e) => e,
        nom::Err::Failure(e) => e,
    }
}

fn parse_test(file: &str) {
    let file = std::fs::read_to_string(file).unwrap();
    let r = whole_program(&file);
    match r {
        Err(e) => println!("{}", nom::error::convert_error(&file, convert(e))),
        Ok((_, parsed)) => {
            println!("{:?}", parsed);
            let (inter_parsed, interner) = parsed.as_interned();
            let pretty = inter_parsed.pretty_print_string(&interner);
            println!("{}", pretty);
            let s = whole_program(&pretty);
            match s {
                Err(e) => println!("{}", nom::error::convert_error(&pretty, convert(e))),
                Ok((_, sparsed)) => {
                    println!("{:?}", sparsed);
                    let (sinter_parsed, sinterner) = parsed.as_interned();
                    println!("{}", sinter_parsed.pretty_print_string(&sinterner));
                    parsed.check_eq(&sparsed)
                }
            }
        }
    }

}
