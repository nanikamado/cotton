mod ast;
mod codegen;
mod parse;

use codegen::compile;
use parse::parse;

pub fn run(source: &str) {
    let code = parse(source).map(|(_, ast)| compile(ast));
    println!("{:?}", code);
}
