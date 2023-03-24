mod ast_step1;
mod ast_step2;
mod ast_step3;
mod ast_step4;
mod ast_step5;
mod ast_step6;
mod codegen;
mod errors;
mod intrinsics;
mod run_js;

use ast_step1::ident_id::IdentId;
use ast_step1::name_id::Path;
use ast_step1::token_map::{TokenMap, TokenMapEntry};
pub use ast_step2::imports::Imports;
pub use ast_step2::type_display::{
    PrintTypeOfGlobalVariableForUser, PrintTypeOfLocalVariableForUser,
};
use ast_step2::types::{Type, TypeMatchableRef, TypeUnit};
use ast_step3::{
    GlobalVariableType, LocalVariableType, ResolvedIdent, VariableId,
};
use codegen::codegen;
use errors::CompileError;
pub use fxhash::FxHashMap;
pub use parser::parse::parse_result;
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
    let ast = parser::parse(source);
    let ast = combine_with_prelude(ast);
    let mut imports = Imports::default();
    let (ast, mut token_map) = ast_step1::Ast::from(&ast, &mut imports)
        .unwrap_or_else(|e| {
            e.write(
                source,
                &mut std::io::stderr(),
                filename,
                &Default::default(),
            )
            .unwrap();
            process::exit(1)
        });
    let (ast, _resolved_idents) = to_step_3(ast, &mut token_map, &mut imports)
        .unwrap_or_else(|e| {
            e.write(source, &mut std::io::stderr(), filename, &imports)
                .unwrap();
            process::exit(1)
        });
    if command == Command::PrintTypes {
        print_types(&ast);
    } else {
        let ast = ast_step4::Ast::from(ast);
        let ast = ast_step5::Ast::from(ast);
        let ast = ast_step6::Ast::from(ast);
        let js = codegen(ast);
        if command == Command::PrintJs {
            println!("{js}");
        } else if command == Command::RunJs {
            run_js::run(&js);
        } else {
            unreachable!()
        }
    }
}

fn to_step_3<'a>(
    ast: ast_step1::Ast<'a>,
    token_map: &mut TokenMap,
    imports: &mut Imports,
) -> Result<(ast_step3::Ast<'a>, FxHashMap<IdentId, ResolvedIdent>), CompileError>
{
    let ast = ast_step2::Ast::from(ast, token_map, imports)?;
    ast_step3::Ast::from(ast, token_map, imports)
}

pub fn combine_with_prelude(ast: parser::Ast) -> parser::Ast {
    let source = include_str!("../../library/prelude.cot");
    let prelude_ast = parser::parse(source);
    parser::Ast {
        decls: vec![
            parser::Decl::Module {
                name: ("pkgroot".to_string(), None, None),
                ast,
                is_public: false,
            },
            parser::Decl::Module {
                name: ("prelude".to_string(), None, None),
                ast: prelude_ast,
                is_public: false,
            },
        ],
    }
}

pub enum TokenKind {
    GlobalVariable(VariableId, Option<GlobalVariableType>),
    LocalVariable(VariableId, (Type, FxHashMap<TypeUnit, Path>)),
    Constructor(Option<GlobalVariableType>),
    Type,
    Interface,
    KeyWord,
    VariableDeclInInterface(GlobalVariableType),
}

pub struct TokenMapWithEnv {
    pub token_map: FxHashMap<TokenId, TokenKind>,
    pub imports: Imports,
}

pub fn get_token_map(
    ast: &parser::Ast,
) -> Result<TokenMapWithEnv, CompileError> {
    let mut imports = Imports::default();
    let (ast, mut token_map) = ast_step1::Ast::from(ast, &mut imports)?;
    let ast = ast_step2::Ast::from(ast, &mut token_map, &mut imports)?;
    let (ast, resolved_idents) =
        ast_step3::Ast::from(ast, &mut token_map, &mut imports)?;
    let token_map = token_map
        .0
        .into_iter()
        .map(|(id, t)| {
            fn variable_id_to_token_kind(
                variable_id: VariableId,
                ast: &ast_step3::Ast,
            ) -> TokenKind {
                use VariableId::*;
                match variable_id {
                    IntrinsicConstructor(_) => TokenKind::Type,
                    Constructor(_) => TokenKind::Constructor(
                        ast.types_of_global_decls.get(&variable_id).cloned(),
                    ),
                    Global(_) | IntrinsicVariable(_) | FieldAccessor { .. } => {
                        TokenKind::GlobalVariable(
                            variable_id,
                            ast.types_of_global_decls
                                .get(&variable_id)
                                .cloned(),
                        )
                    }
                    Local(_) => {
                        let LocalVariableType { t, toplevel } =
                            &ast.types_of_local_decls[&variable_id];
                        TokenKind::LocalVariable(
                            variable_id,
                            (
                                t.clone(),
                                ast.types_of_global_decls
                                    [&VariableId::Global(*toplevel)]
                                    .fixed_parameters
                                    .clone(),
                            ),
                        )
                    }
                }
            }
            let t = match t {
                TokenMapEntry::Decl(decl_id) => {
                    if let Some(t) = ast
                        .types_of_global_decls
                        .get(&VariableId::Global(decl_id))
                    {
                        TokenKind::GlobalVariable(
                            VariableId::Global(decl_id),
                            Some(t.clone()),
                        )
                    } else {
                        let LocalVariableType { t, toplevel } = &ast
                            .types_of_local_decls[&VariableId::Local(decl_id)];
                        TokenKind::LocalVariable(
                            VariableId::Local(decl_id),
                            (
                                t.clone(),
                                ast.types_of_global_decls
                                    [&VariableId::Global(*toplevel)]
                                    .fixed_parameters
                                    .clone(),
                            ),
                        )
                    }
                }
                TokenMapEntry::ResolvedIdent(variable_id) => {
                    variable_id_to_token_kind(variable_id, &ast)
                }
                TokenMapEntry::Ident(ident_id) => {
                    let r = resolved_idents.get(&ident_id).unwrap();
                    variable_id_to_token_kind(r.variable_id, &ast)
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
                                .get(&VariableId::Constructor(decl_id))
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
    Ok(TokenMapWithEnv { token_map, imports })
}

pub fn print_types(ast: &ast_step3::Ast) {
    for d in &ast.variable_decls {
        println!(
            "{} : {}",
            d.name,
            &ast.types_of_global_decls[&VariableId::Global(d.decl_id)].t
        );
    }
}
