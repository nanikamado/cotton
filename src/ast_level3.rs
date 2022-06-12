mod type_check;
pub mod type_util;

use self::type_check::{type_check, ResolvedIdents, VariableId};
use crate::ast_level2::{
    self,
    decl_id::DeclId,
    ident_id::IdentId,
    types::{Type, TypeVariable},
    DataDecl, IncompleteType, Pattern,
};
use fxhash::FxHashMap;
use itertools::Itertools;

/// # Difference between `ast_level2::Ast` and `ast_level3::Ast`
/// - The names of variables are resolved.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
    pub type_map: Vec<(IdentId, Type<'a>)>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_: IncompleteType<'a>,
    pub value: Expr<'a>,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: &'a str,
        variable_id: VariableId,
        type_args: Vec<(TypeVariable, Type<'a>)>,
    },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub exprs: Vec<Expr<'a>>,
}

impl<'a> From<ast_level2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_level2::Ast<'a>) -> Self {
        let (resolved_idents, types_of_decls, type_map) =
            type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        for (ident, t) in &type_map {
            log::debug!("{ident} : {t}");
        }
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(move |d| {
                variable_decl(d, &resolved_idents, &types_of_decls)
            })
            .collect();
        for v in &variable_decl {
            log::debug!("type_ {} : {}", v.name, v.type_);
        }
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
            type_map,
        }
    }
}

fn variable_decl<'a>(
    d: ast_level2::VariableDecl<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
) -> VariableDecl<'a> {
    let type_ = if let Some(t) = d.type_annotation {
        t
    } else {
        types_of_decls.get(&d.decl_id).unwrap().clone()
    };
    VariableDecl {
        name: d.name,
        type_,
        value: expr(d.value, resolved_idents, types_of_decls),
        decl_id: d.decl_id,
    }
}

fn expr<'a>(
    e: ast_level2::Expr<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
) -> Expr<'a> {
    use Expr::*;
    match e {
        ast_level2::Expr::Lambda(a) => Lambda(
            a.into_iter()
                .map(|arm| {
                    fn_arm(arm, resolved_idents, types_of_decls)
                })
                .collect(),
        ),
        ast_level2::Expr::Number(a) => Number(a),
        ast_level2::Expr::StrLiteral(a) => StrLiteral(a),
        ast_level2::Expr::Ident { name, ident_id } => {
            let (variable_id, type_args) = resolved_idents
                .get(&ident_id)
                .unwrap_or_else(|| {
                    panic!(
                        "{:?} not found in resolved_idents. \
                        name: {:?}",
                        ident_id, name
                    )
                })
                .clone();
            log::debug!(
                "{} -- {} -- [{}]",
                name,
                ident_id,
                type_args.iter().format_with(", ", |(v, t), f| f(
                    &format!("({v} ~> {t})")
                ))
            );
            Ident {
                name,
                variable_id,
                type_args,
            }
        }
        ast_level2::Expr::Decl(a) => Decl(Box::new(variable_decl(
            *a,
            resolved_idents,
            types_of_decls,
        ))),
        ast_level2::Expr::Call(f, a) => Call(
            expr(*f, resolved_idents, types_of_decls).into(),
            expr(*a, resolved_idents, types_of_decls).into(),
        ),
    }
}

fn fn_arm<'a>(
    arm: ast_level2::FnArm<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
) -> FnArm<'a> {
    FnArm {
        pattern: arm.pattern,
        pattern_type: arm.pattern_type,
        exprs: arm
            .exprs
            .into_iter()
            .map(|a| expr(a, resolved_idents, types_of_decls))
            .collect(),
    }
}
