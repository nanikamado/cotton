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

pub use ast_step1::OpPrecedenceMap;
use ast_step2::types::Type;
pub use ast_step2::{
    types::TypeMatchableRef, IncompleteType, PrintTypeOfGlobalVariableForUser,
    PrintTypeOfLocalVariableForUser,
};
use ast_step3::VariableId;
use codegen::codegen;
pub use fxhash::FxHashMap;
pub use parser::token_id::TokenId;
pub use parser::{lex, parse::parse, Token};
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
    let ast = parser::parse::parse(tokens, source, src_len);
    let (ast, _) = ast_step1::Ast::from(&ast);
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
    GlobalVariable(VariableId, Option<IncompleteType<'a>>),
    LocalVariable(VariableId, Option<Type<'a>>),
    Constructor(Option<IncompleteType<'a>>),
    Type,
    Interface,
    VariableDeclInInterface(IncompleteType<'a>),
}

pub struct TokenMapWithEnv<'a> {
    pub token_map: FxHashMap<TokenId, TokenKind<'a>>,
    pub op_precedence_map: OpPrecedenceMap<'a>,
}

pub fn get_token_map(ast: &parser::Ast) -> TokenMapWithEnv {
    let (ast, op_precedence_map) = ast_step1::Ast::from(ast);
    let (ast, token_map) = ast_step2::Ast::from(ast);
    let (ast, resolved_idents) = ast_step3::Ast::from(ast);
    let token_map = token_map
        .0
        .into_iter()
        .map(|(id, t)| {
            let t = match t {
                ast_step2::TokenMapEntry::Decl(decl_id) => {
                    if let Some(t) = ast
                        .types_of_global_decls
                        .get(&VariableId::Decl(decl_id))
                    {
                        TokenKind::GlobalVariable(
                            VariableId::Decl(decl_id),
                            Some(t.clone()),
                        )
                    } else {
                        let t = ast
                            .types_of_local_decls
                            .get(&VariableId::Decl(decl_id));
                        TokenKind::LocalVariable(
                            VariableId::Decl(decl_id),
                            t.cloned(),
                        )
                    }
                }
                ast_step2::TokenMapEntry::Ident(ident_id) => {
                    let r = resolved_idents.get(&ident_id).unwrap();
                    match r.variable_kind {
                        ast_step4::VariableKind::IntrinsicConstructor => {
                            TokenKind::Type
                        }
                        ast_step4::VariableKind::Constructor => {
                            TokenKind::Constructor(
                                ast.types_of_global_decls
                                    .get(&r.variable_id)
                                    .cloned(),
                            )
                        }
                        ast_step4::VariableKind::Global
                        | ast_step4::VariableKind::Intrinsic => {
                            TokenKind::GlobalVariable(
                                r.variable_id,
                                ast.types_of_global_decls
                                    .get(&r.variable_id)
                                    .cloned(),
                            )
                        }
                        ast_step4::VariableKind::Local => {
                            TokenKind::LocalVariable(
                                r.variable_id,
                                ast.types_of_local_decls
                                    .get(&r.variable_id)
                                    .cloned(),
                            )
                        }
                    }
                }
                ast_step2::TokenMapEntry::VariableDeclInInterface(t) => {
                    TokenKind::VariableDeclInInterface(t.into())
                }
                ast_step2::TokenMapEntry::DataDecl(_)
                | ast_step2::TokenMapEntry::TypeId(_)
                | ast_step2::TokenMapEntry::TypeAlias
                | ast_step2::TokenMapEntry::TypeVariable => TokenKind::Type,
                ast_step2::TokenMapEntry::Constructor(id) => match id {
                    ast_step2::ConstructorId::DeclId(decl_id) => {
                        TokenKind::Constructor(
                            ast.types_of_global_decls
                                .get(&VariableId::Decl(decl_id))
                                .cloned(),
                        )
                    }
                    ast_step2::ConstructorId::Intrinsic(id) => {
                        TokenKind::Constructor(Some(id.to_type().into()))
                    }
                },
                ast_step2::TokenMapEntry::Interface => TokenKind::Interface,
            };
            (id, t)
        })
        .collect();
    TokenMapWithEnv {
        token_map,
        op_precedence_map,
    }
}
