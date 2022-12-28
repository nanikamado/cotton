mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod ast_step5;
mod codegen;
mod errors;
mod intrinsics;
mod run_js;
mod rust_backend;

use ast_step1::ident_id::IdentId;
use ast_step1::name_id::Name;
use ast_step1::token_map::{TokenMap, TokenMapEntry};
pub use ast_step1::OpPrecedenceMap;
pub use ast_step2::type_display::{
    PrintTypeOfGlobalVariableForUser, PrintTypeOfLocalVariableForUser,
};
use ast_step2::types::{Type, TypeMatchableRef, TypeUnit};
use ast_step3::{
    GlobalVariableType, LocalVariableType, ResolvedIdent, VariableId,
    VariableKind,
};
use codegen::codegen;
use errors::CompileError;
pub use fxhash::FxHashMap;
pub use parser::parse::{parse, parse_result};
pub use parser::token_id::TokenId;
pub use parser::{lex, Token};
use simplelog::{
    self, ColorChoice, ConfigBuilder, LevelFilter, TermLogger, TerminalMode,
};
use std::io::ErrorKind;
use std::process::{self, exit, Stdio};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Command {
    RunJs,
    RunRust,
    PrintJs,
    PrintTypes,
}

pub fn run(
    source: &str,
    filename: &str,
    command: Command,
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
    let ast = combine_with_prelude(ast);
    let (ast, op_precedence_map, mut token_map) = ast_step1::Ast::from(&ast);
    let (ast, _resolved_idents) = to_step_3(ast, &mut token_map)
        .unwrap_or_else(|e| {
            e.write(
                source,
                &mut std::io::stderr(),
                filename,
                &op_precedence_map,
            )
            .unwrap();
            process::exit(1)
        });
    if command == Command::PrintTypes {
        print_types(&ast);
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

fn to_step_3(
    ast: ast_step1::Ast,
    token_map: &mut TokenMap,
) -> Result<(ast_step3::Ast, FxHashMap<IdentId, ResolvedIdent>), CompileError> {
    let ast = ast_step2::Ast::from(ast, token_map)?;
    ast_step3::Ast::from(ast)
}

pub fn combine_with_prelude(ast: parser::Ast) -> parser::Ast {
    let source = include_str!("../../library/prelude.cot");
    let (tokens, src_len) = parser::lex(source);
    let prelude_ast = parser::parse::parse(tokens, source, src_len);
    parser::Ast {
        decls: vec![
            parser::Decl::Module {
                name: ("pkgroot".to_string(), None),
                ast,
                is_public: false,
            },
            parser::Decl::Module {
                name: ("prelude".to_string(), None),
                ast: prelude_ast,
                is_public: false,
            },
        ],
    }
}

pub enum TokenKind {
    GlobalVariable(VariableId, Option<GlobalVariableType>),
    LocalVariable(VariableId, Option<(Type, FxHashMap<TypeUnit, Name>)>),
    Constructor(Option<GlobalVariableType>),
    Type,
    Interface,
    KeyWord,
    VariableDeclInInterface(GlobalVariableType),
}

pub struct TokenMapWithEnv<'a> {
    pub token_map: FxHashMap<TokenId, TokenKind>,
    pub op_precedence_map: OpPrecedenceMap<'a>,
}

pub fn get_token_map(
    ast: &parser::Ast,
) -> Result<TokenMapWithEnv, CompileError> {
    let (ast, op_precedence_map, mut token_map) = ast_step1::Ast::from(ast);
    let ast = ast_step2::Ast::from(ast, &mut token_map)?;
    let (ast, resolved_idents) = ast_step3::Ast::from(ast)?;
    let token_map = token_map
        .0
        .into_iter()
        .map(|(id, t)| {
            let t = match t {
                TokenMapEntry::Decl(decl_id) => {
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
                            t.map(|LocalVariableType { t, toplevel }| {
                                (
                                    t.clone(),
                                    ast.types_of_global_decls
                                        [&VariableId::Decl(*toplevel)]
                                        .fixed_parameters
                                        .clone(),
                                )
                            }),
                        )
                    }
                }
                TokenMapEntry::Ident(ident_id) => {
                    let r = resolved_idents.get(&ident_id).unwrap();
                    match r.variable_kind {
                        VariableKind::IntrinsicConstructor => TokenKind::Type,
                        VariableKind::Constructor => TokenKind::Constructor(
                            ast.types_of_global_decls
                                .get(&r.variable_id)
                                .cloned(),
                        ),
                        VariableKind::Global | VariableKind::Intrinsic => {
                            TokenKind::GlobalVariable(
                                r.variable_id,
                                ast.types_of_global_decls
                                    .get(&r.variable_id)
                                    .cloned(),
                            )
                        }
                        VariableKind::Local => TokenKind::LocalVariable(
                            r.variable_id,
                            ast.types_of_local_decls.get(&r.variable_id).map(
                                |LocalVariableType { t, toplevel }| {
                                    (
                                        t.clone(),
                                        ast.types_of_global_decls
                                            [&VariableId::Decl(*toplevel)]
                                            .fixed_parameters
                                            .clone(),
                                    )
                                },
                            ),
                        ),
                    }
                }
                TokenMapEntry::VariableDeclInInterface(t) => {
                    TokenKind::VariableDeclInInterface(GlobalVariableType {
                        t,
                        fixed_parameters: Default::default(),
                    })
                }
                TokenMapEntry::DataDecl(_)
                | TokenMapEntry::TypeId(_)
                | TokenMapEntry::TypeAlias
                | TokenMapEntry::TypeVariable => TokenKind::Type,
                TokenMapEntry::Constructor(id) => match id {
                    ast_step2::ConstructorId::DeclId(decl_id) => {
                        TokenKind::Constructor(
                            ast.types_of_global_decls
                                .get(&VariableId::Decl(decl_id))
                                .cloned(),
                        )
                    }
                    ast_step2::ConstructorId::Intrinsic(id) => {
                        TokenKind::Constructor(Some(GlobalVariableType {
                            t: id.to_type(),
                            fixed_parameters: Default::default(),
                        }))
                    }
                },
                TokenMapEntry::Interface => TokenKind::Interface,
                TokenMapEntry::KeyWord => TokenKind::KeyWord,
            };
            (id, t)
        })
        .collect();
    Ok(TokenMapWithEnv {
        token_map,
        op_precedence_map,
    })
}

pub fn print_types(ast: &ast_step3::Ast) {
    for d in &ast.variable_decl {
        println!(
            "{} : {}",
            d.name,
            &ast.types_of_global_decls[&VariableId::Decl(d.decl_id)].t
        );
    }
}
