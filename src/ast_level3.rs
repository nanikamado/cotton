mod type_check;
pub mod type_util;

use self::type_check::{
    type_check, ResolvedIdents, TypeVariableTracker, VariableId,
};
use crate::ast_level2::{
    self,
    decl_id::DeclId,
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
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_: IncompleteType<'a>,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, Type<'a>);

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
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub expr: ExprWithType<'a>,
}

impl<'a> From<ast_level2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_level2::Ast<'a>) -> Self {
        let (resolved_idents, types_of_decls, mut type_map) =
            type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        log::debug!("type_variable_tracker: {}", type_map);
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(move |d| {
                variable_decl(
                    d,
                    &resolved_idents,
                    &types_of_decls,
                    &mut type_map,
                )
            })
            .collect();
        for v in &variable_decl {
            log::debug!("type_ {} : {}", v.name, v.type_);
        }
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
        }
    }
}

fn variable_decl<'a>(
    d: ast_level2::VariableDecl<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> VariableDecl<'a> {
    let decl_type = types_of_decls.get(&d.decl_id).unwrap();
    assert_eq!(0, decl_type.variable_requirements.len());
    VariableDecl {
        name: d.name,
        type_: IncompleteType {
            constructor: type_variable_tracker
                .normalize_type(decl_type.constructor.clone()),
            variable_requirements: Vec::new(),
            subtype_relation: decl_type
                .subtype_relation
                .iter()
                .map(|(a, b)| {
                    (
                        type_variable_tracker
                            .normalize_type(a.clone()),
                        type_variable_tracker
                            .normalize_type(b.clone()),
                    )
                })
                .collect(),
        },
        value: expr(
            d.value,
            resolved_idents,
            types_of_decls,
            type_variable_tracker,
        ),
        decl_id: d.decl_id,
    }
}

fn expr<'a>(
    (e, t): ast_level2::ExprWithType<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> ExprWithType<'a> {
    use Expr::*;
    let e = match e {
        ast_level2::Expr::Lambda(a) => Lambda(
            a.into_iter()
                .map(|arm| {
                    fn_arm(
                        arm,
                        resolved_idents,
                        types_of_decls,
                        type_variable_tracker,
                    )
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
            type_variable_tracker,
        ))),
        ast_level2::Expr::Call(f, a) => Call(
            expr(
                *f,
                resolved_idents,
                types_of_decls,
                type_variable_tracker,
            )
            .into(),
            expr(
                *a,
                resolved_idents,
                types_of_decls,
                type_variable_tracker,
            )
            .into(),
        ),
    };
    (e, type_variable_tracker.find(t))
}

fn fn_arm<'a>(
    arm: ast_level2::FnArm<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> FnArm<'a> {
    let exprs: Vec<_> = arm
        .exprs
        .into_iter()
        .map(|a| {
            expr(
                a,
                resolved_idents,
                types_of_decls,
                type_variable_tracker,
            )
        })
        .collect();
    let last_type = exprs[exprs.len() - 1].1.clone();
    FnArm {
        pattern: arm.pattern,
        pattern_type: arm.pattern_type,
        expr: (Expr::DoBlock(exprs), last_type),
    }
}
