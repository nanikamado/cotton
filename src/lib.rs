mod ast;
mod ast2;
mod codegen;
mod parse;

use parse::parse;
use codegen::compile;

pub fn run(source: &str) {
    let ast: ast2::AST =
        parse(source).map(|(_, ast)| ast.into()).unwrap();
    println!("{}", compile(ast));
}
