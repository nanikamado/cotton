mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod codegen;
mod intrinsics;
mod rust_backend;

use codegen::codegen;
use simplelog::{
    self, ColorChoice, ConfigBuilder, LevelFilter, TermLogger,
    TerminalMode,
};
use std::{
    io::{ErrorKind, Write},
    process::{exit, Command, Stdio},
};

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
    let ast = parse::parse(source);
    let ast: ast_step1::Ast = (&ast).into();
    let ast: ast_step2::Ast = ast.into();
    let ast: ast_step3::Ast = ast.into();
    let ast: ast_step4::Ast = ast.into();
    if use_rust_backend {
        rust_backend::run(ast);
    } else {
        let js = codegen(ast);
        if output_js {
            println!("{}", js);
        } else {
            let mut child = Command::new("node")
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
