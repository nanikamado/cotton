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
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub ident: String,
    pub type_annotation: Option<IncompleteType>,
    pub value: Expr,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Ident {
        name: String,
        variable_id: VariableId,
    },
    Decl(Box<VariableDecl>),
    Call(Box<Expr>, Box<Expr>),
    Unit,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub pattern_type: Vec<Option<Type>>,
    pub exprs: Vec<Expr>,
}

impl From<ast2::Ast> for Ast {
    fn from(ast: ast2::Ast) -> Self {
        let resolved_idents = type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        Self {
            variable_decl: ast
                .variable_decl
                .into_iter()
                .map(|d| variable_decl(d, &resolved_idents))
                .collect(),
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
        }
    }
}

fn variable_decl(
    d: ast2::VariableDecl,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> VariableDecl {
    VariableDecl {
        ident: d.ident,
        type_annotation: d.type_annotation,
        value: expr(d.value, resolved_idents),
        decl_id: d.decl_id,
    }
}

fn expr(
    e: ast2::Expr,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> Expr {
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
        ast2::Expr::Unit => Unit,
    }
}

fn fn_arm(
    arm: ast2::FnArm,
    resolved_idents: &FxHashMap<IdentId, VariableId>,
) -> FnArm {
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
