mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod codegen;
mod intrinsics;
mod lex;
mod parse;
mod rust_backend;

use codegen::codegen;
use parse::parse;
use simplelog::{
    self, ColorChoice, ConfigBuilder, LevelFilter, TermLogger,
    TerminalMode,
};
use std::{
    io::ErrorKind,
    process::{exit, Command, Stdio},
};

use crate::lex::lex;

pub fn run(
    source: &str,
    output_js: bool,
    use_rust_backend: bool,
    loglevel: LevelFilter,
) {
    TermLogger::init(
        loglevel,
        ConfigBuilder::new()
            .set_location_level(LevelFilter::Error)
            .set_time_level(LevelFilter::Off)
            .set_thread_level(LevelFilter::Off)
            .set_target_level(LevelFilter::Off)
            .build(),
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
    let (tokens, src_len) = lex(source);
    let ast = parse(tokens, source, src_len);
    let ast: ast_step1::Ast = (&ast).into();
    let ast: ast_step2::Ast = ast.into();
    let ast: ast_step3::Ast = ast.into();
    let ast: ast_step4::Ast = ast.into();
    dbg!(&ast);
    if use_rust_backend {
        rust_backend::run(ast);
    } else {
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
    }
}
