mod ast;
mod ast2;
mod codegen;
mod parse;

// use codegen::compile;
use parse::parse;

pub fn run(source: &str) {
    let code: ast2::AST = parse(source).map(|(_, ast)| ast.into()).unwrap();
    dbg!(code);
    // println!("{:?}", code);
}
