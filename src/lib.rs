mod ast0;
mod ast1;
mod codegen;
mod name_conversion;
mod parse;
mod type_check;
mod type_variable;

use codegen::compile;
use parse::parse;
use type_check::type_check;

pub fn run(source: &str) {
    let (remaining, ast) = parse(source).unwrap();
    if remaining.is_empty() {
        let ast: ast1::Ast = ast.into();
        let resolved_idents = type_check(&ast);
        let ast = name_conversion::run(ast, &resolved_idents);
        dbg!(&ast);
        println!("{}", compile(ast));
    } else {
        eprintln!(
            "unexpected input:\n{}\nast:\n{:?}",
            remaining, ast
        );
    }
}
