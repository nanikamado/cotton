mod ast0;
mod ast1;
mod ast2;
mod ast3;
mod codegen;
mod parse;
mod type_check;
mod type_variable;

use codegen::codegen;
use parse::parse;
use simplelog::{
    self, ColorChoice, Config, LevelFilter, TermLogger, TerminalMode,
};
use std::{
    io::ErrorKind,
    process::{exit, Command, Stdio},
};

pub fn run(source: &str, output_js: bool, loglevel: LevelFilter) {
    TermLogger::init(
        loglevel,
        Config::default(),
        TerminalMode::Stderr,
        ColorChoice::Auto,
    )
    .unwrap();
    if !output_js {
        match Command::new("node")
            .arg("--version")
            .stdout(Stdio::null())
            .spawn()
        {
            Ok(_) => (),
            Err(e) => {
                match e.kind() {
                    ErrorKind::NotFound => eprintln!(
                        "node command not found. \
                        You need to install node."
                    ),
                    _ => eprintln!("failed to run node"),
                };
                exit(1)
            }
        }
    }
    let (remaining, ast) = parse(source).unwrap();
    if remaining.is_empty() {
        let ast: ast1::Ast = ast.into();
        let ast: ast2::Ast = ast.into();
        let ast: ast3::Ast = ast.into();
        log::trace!("{:?}", ast);
        let js = codegen(ast);
        if output_js {
            println!("{}", js);
        } else {
            Command::new("node")
                .arg("--eval")
                .arg(js)
                .spawn()
                .unwrap()
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
