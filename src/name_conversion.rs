use crate::{
    ast2::{ident_id::IdentId, Ast, Expr, FnArm, VariableDecl},
    type_check::VariableId,
};
use fxhash::FxHashMap;

pub fn run(
    mut ast: Ast,
    idents: &FxHashMap<IdentId, VariableId>,
) -> Ast {
    ast.entry_point = ast
        .variable_decl
        .iter()
        .find(|d| d.ident == "main")
        .map(|d| d.decl_id);
    ast.variable_decl = ast
        .variable_decl
        .into_iter()
        .map(|d| decl(d, idents))
        .collect();
    ast
}

fn decl(
    mut d: VariableDecl,
    idents: &FxHashMap<IdentId, VariableId>,
) -> VariableDecl {
    d.value = expr(d.value, idents);
    d
}

fn expr(e: Expr, idents: &FxHashMap<IdentId, VariableId>) -> Expr {
    match e {
        Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter().map(|a| fn_arm(a, idents)).collect(),
        ),
        Expr::Ident {
            name: info,
            ident_id,
            decl_id: _,
        } => Expr::Ident {
            name: info,
            ident_id,
            decl_id: idents.get(&ident_id).copied(),
        },
        Expr::Decl(d) => Expr::Decl(Box::new(decl(*d, idents))),
        Expr::Call(a, b) => Expr::Call(
            Box::new(expr(*a, idents)),
            Box::new(expr(*b, idents)),
        ),
        other => other,
    }
}

fn fn_arm(
    mut arm: FnArm,
    idents: &FxHashMap<IdentId, VariableId>,
) -> FnArm {
    arm.exprs =
        arm.exprs.into_iter().map(|e| expr(e, idents)).collect();
    arm
}
