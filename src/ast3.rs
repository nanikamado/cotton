use crate::{
    ast2::{self, DataDecl, Pattern},
    ast2::{
        decl_id::DeclId, ident_id::IdentId, types::Type,
        IncompleteType,
    },
    type_check::{type_check, VariableId},
};
use fxhash::FxHashMap;

#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub ident: &'a str,
    pub type_annotation: Option<IncompleteType<'a>>,
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

impl<'a> From<ast2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast2::Ast<'a>) -> Self {
        let resolved_idents = type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        Self {
            variable_decl: ast
                .variable_decl
                .into_iter()
                .map(move |d| variable_decl(d, &resolved_idents))
                .collect(),
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
        }
    }
}

fn variable_decl<'a>(
    d: ast2::VariableDecl<'a>,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> VariableDecl<'a> {
    VariableDecl {
        ident: d.ident,
        type_annotation: d.type_annotation,
        value: expr(d.value, resolved_idents),
        decl_id: d.decl_id,
    }
}

fn expr<'a>(
    e: ast2::Expr<'a>,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> Expr<'a> {
    use Expr::*;
    match e {
        ast2::Expr::Lambda(a) => Lambda(
            a.into_iter()
                .map(|arm| fn_arm(arm, resolved_idents))
                .collect(),
        ),
        ast2::Expr::Number(a) => Number(a),
        ast2::Expr::StrLiteral(a) => StrLiteral(a),
        ast2::Expr::Ident { name, ident_id } => Ident {
            name,
            variable_id: *resolved_idents.get(&ident_id).unwrap(),
        },
        ast2::Expr::Decl(a) => {
            Decl(Box::new(variable_decl(*a, resolved_idents)))
        }
        ast2::Expr::Call(f, a) => Call(
            expr(*f, resolved_idents).into(),
            expr(*a, resolved_idents).into(),
        ),
    }
}

fn fn_arm<'a>(
    arm: ast2::FnArm<'a>,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> FnArm<'a> {
    FnArm {
        pattern: arm.pattern,
        pattern_type: arm.pattern_type,
        exprs: arm
            .exprs
            .into_iter()
            .map(|a| expr(a, resolved_idents))
            .collect(),
    }
}
