use std::{fs, io};
use langlang::{parser};

#[derive(Debug)]
enum Error {
    InputError(String),
    IOError(String),
    ParsingError(String),
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::IOError(e.to_string())
    }
}

impl From<langlang::parser::Error> for Error {
    fn from(e: langlang::parser::Error) -> Self {
        Error::ParsingError(e.to_string())
    }
}

fn main() -> Result<(), Error> {
    env_logger::init();

    let mut args = std::env::args();
    if args.len() != 2 {
        println!("Usage: {} GRAMMAR-FILE", args.nth(0).unwrap());
        return Err(Error::InputError("Grammar file not provided".to_string()));
    }

    let grammar_file = args.nth(1).unwrap();
    let grammar_data = fs::read_to_string(grammar_file)?;
    let mut c = parser::Compiler::new();
    c.compile_str(grammar_data.as_str())?;

    let p = c.program();
    println!("Compiled:\n{}", p.to_string());

    Ok(())
}
