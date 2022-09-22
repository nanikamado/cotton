mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod ast_step5;
mod ast_step6;
mod codegen;
mod intrinsics;
mod rust_backend;

use ast_step3::type_check;
use codegen::codegen;
use simplelog::{
    self, ColorChoice, ConfigBuilder, LevelFilter, TermLogger, TerminalMode,
};
use std::{
    io::{ErrorKind, Write},
    process::{self, exit, Stdio},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Command {
    RunJs,
    RunRust,
    PrintJs,
    PrintTypes,
}

pub fn run(source: &str, command: Command, loglevel: LevelFilter) {
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
    if command == Command::RunJs {
        match process::Command::new("node")
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
    let ast = parse::parse(source);
    let ast = ast_step1::Ast::from(&ast);
    let ast = ast_step2::Ast::from(ast);
    let (resolved_idents, _types_of_decls, _subtype_relations, _map) =
        type_check(&ast);
    let ast = ast_step3::Ast::from(ast, &resolved_idents);
    let ast = ast_step4::Ast::from(ast, &resolved_idents);
    let ast = ast_step5::Ast::from(ast);
    let ast = ast_step6::Ast::from(ast);
    if command == Command::RunRust {
        rust_backend::run(ast);
    } else {
        let js = codegen(ast);
        if command == Command::PrintJs {
            println!("{}", js);
        } else {
            let mut child = process::Command::new("node")
                .stdin(Stdio::piped())
                .spawn()
                .unwrap();
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(js.as_bytes())
                .unwrap();
            child.wait().unwrap();
        }
    }
}
