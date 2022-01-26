mod ast0;
mod ast1;
mod codegen;
mod name_conversion;
mod parse;
mod type_check;
mod type_variable;

use codegen::codegen;
use log;
use parse::parse;
use simplelog::{
    self, ColorChoice, Config, LevelFilter, TermLogger, TerminalMode,
};
use std::process::Command;
use type_check::type_check;

pub fn run(source: &str, output_js: bool, loglevel: LevelFilter) {
    TermLogger::init(
        loglevel,
        Config::default(),
        TerminalMode::Stderr,
        ColorChoice::Auto,
    )
    .unwrap();
    let (remaining, ast) = parse(source).unwrap();
    if remaining.is_empty() {
        let ast: ast1::Ast = ast.into();
        let resolved_idents = type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        let ast = name_conversion::run(ast, &resolved_idents);
        log::trace!("{:?}", ast);
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
