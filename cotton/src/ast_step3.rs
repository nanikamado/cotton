mod type_check;
pub mod type_util;

pub use self::type_check::{
    simplify_subtype_rel, type_check, ResolvedIdents, TypeVariableMap,
    VariableId, VariableRequirement,
};
use crate::ast_step2::ident_id::IdentId;
use crate::ast_step2::{self, decl_id::DeclId, DataDecl, Pattern};
pub use crate::ast_step3::type_check::ResolvedIdent;

/// # Difference between `ast_step2::Ast` and `ast_step3::Ast`
/// - The names of variables are resolved.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
    pub resolved_idents: ResolvedIdents<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: Expr<'a>,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident { name: &'a str, ident_id: IdentId },
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Do(Vec<Expr<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: Expr<'a>,
}

impl<'a> From<ast_step2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step2::Ast<'a>) -> Self {
        let (resolved_idents, _types_of_decls, _subtype_relations, _map) =
            type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| variable_decl(d, &resolved_idents))
            .collect();
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
            resolved_idents,
        }
    }
}

fn variable_decl<'a>(
    d: ast_step2::VariableDecl<'a>,
    resolved_idents: &ResolvedIdents<'a>,
) -> VariableDecl<'a> {
    let value = expr(d.value, resolved_idents);
    VariableDecl {
        name: d.name,
        value,
        decl_id: d.decl_id,
    }
}

fn expr<'a>(
    (e, _): ast_step2::ExprWithType<'a>,
    resolved_idents: &ResolvedIdents<'a>,
) -> Expr<'a> {
    use Expr::*;
    let e = match e {
        ast_step2::Expr::Lambda(a) => Lambda(
            a.into_iter()
                .map(|arm| fn_arm(arm, resolved_idents))
                .collect(),
        ),
        ast_step2::Expr::Number(a) => Number(a),
        ast_step2::Expr::StrLiteral(a) => StrLiteral(a),
        ast_step2::Expr::Ident { name, ident_id } => Ident { name, ident_id },
        ast_step2::Expr::Call(f, a) => Call(
            expr(*f, resolved_idents).into(),
            expr(*a, resolved_idents).into(),
        ),
        ast_step2::Expr::Do(es) => {
            Do(es.into_iter().map(|et| expr(et, resolved_idents)).collect())
        }
    };
    e
}

fn fn_arm<'a>(
    arm: ast_step2::FnArm<'a>,
    resolved_idents: &ResolvedIdents<'a>,
) -> FnArm<'a> {
    let expr = expr(arm.expr, resolved_idents);
    FnArm {
        pattern: arm.pattern,
        expr,
    }
}
