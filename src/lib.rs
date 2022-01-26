mod ast0;
mod ast1;
mod codegen;
mod name_conversion;
mod parse;
mod type_check;
mod type_variable;

use codegen::codegen;
use parse::parse;
use std::process::Command;
use type_check::type_check;

pub fn run(source: &str, output_js: bool) {
    let (remaining, ast) = parse(source).unwrap();
    if remaining.is_empty() {
        let ast: ast1::Ast = ast.into();
        let resolved_idents = type_check(&ast);
        // dbg!(&resolved_idents);
        let ast = name_conversion::run(ast, &resolved_idents);
        // dbg!(&ast);
        let js = codegen(ast);
        if output_js {
            println!("{}", js);
        } else {
            Command::new("node")
                .arg("--eval")
                .arg(js)
                .spawn()
                .expect("faild to run node")
                .wait()
                .unwrap();
        }
    } else {
        eprintln!(
            "unexpected input:\n{}\nast:\n{:?}",
            remaining, ast
        );
    }
}
