mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod ast_step5;
mod codegen;
mod intrinsics;
mod print_types;
mod run_js;
mod rust_backend;

pub use ast_step2::{types::TypeMatchableRef, IncompleteType};
use ast_step3::VariableId;
use codegen::codegen;
use fxhash::FxHashMap;
use parse::token_id::TokenId;
pub use parse::{lex, parse::parse, Token};
use simplelog::{
    self, ColorChoice, ConfigBuilder, LevelFilter, TermLogger, TerminalMode,
};
use std::{
    io::ErrorKind,
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
    let (tokens, src_len) = lex(source);
    let ast = parse::parse::parse(tokens, source, src_len);
    let ast = ast_step1::Ast::from(&ast);
    let (ast, _token_map) = ast_step2::Ast::from(ast);
    let (ast, _resolved_idents) = ast_step3::Ast::from(ast);
    if command == Command::PrintTypes {
        print_types::print(&ast);
    } else {
        let ast = ast_step4::Ast::from(ast);
        let ast = ast_step5::Ast::from(ast);
        if command == Command::RunRust {
            rust_backend::run(ast);
        } else {
            let js = codegen(ast);
            if command == Command::PrintJs {
                println!("{}", js);
            } else if command == Command::RunJs {
                run_js::run(&js);
            } else {
                unreachable!()
            }
        }
    }
}

pub enum TokenKind<'a> {
    Variable(VariableId, Option<IncompleteType<'a>>),
    Type,
}

pub fn get_token_map(ast: &parse::Ast) -> FxHashMap<TokenId, TokenKind> {
    let ast = ast_step1::Ast::from(ast);
    let (ast, token_map) = ast_step2::Ast::from(ast);
    let (ast, resolved_idents) = ast_step3::Ast::from(ast);
    token_map
        .0
        .into_iter()
        .map(|(id, t)| {
            let t = match t {
                ast_step2::TokenMapEntry::Decl(decl_id) => {
                    let t = ast.types_of_decls.get(&VariableId::Decl(decl_id));
                    TokenKind::Variable(VariableId::Decl(decl_id), t.cloned())
                }
                ast_step2::TokenMapEntry::DataDecl(_) => TokenKind::Type,
                ast_step2::TokenMapEntry::Ident(ident_id) => {
                    let r = resolved_idents.get(&ident_id).unwrap();
                    match r.variable_kind {
                        ast_step4::VariableKind::Constructor => TokenKind::Type,
                        _ => TokenKind::Variable(
                            r.variable_id,
                            ast.types_of_decls.get(&r.variable_id).cloned(),
                        ),
                    }
                }
                ast_step2::TokenMapEntry::TypeId(_)
                | ast_step2::TokenMapEntry::TypeAlias => TokenKind::Type,
            };
            (id, t)
        })
        .collect()
}
