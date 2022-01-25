use crate::ast1::{
    decl_id::DeclId, ident_id::IdentId, Ast, Declaration, Expr, FnArm,
};
use fxhash::FxHashMap;

pub fn run(mut ast: Ast, idents: &FxHashMap<IdentId, DeclId>) -> Ast {
    ast.entry_point = ast
        .declarations
        .iter()
        .find(|d| d.identifier == "main")
        .map(|d| d.decl_id);
    ast.declarations = ast
        .declarations
        .into_iter()
        .map(|d| declaration(d, idents))
        .collect();
    ast
}

fn declaration(
    mut d: Declaration,
    idents: &FxHashMap<IdentId, DeclId>,
) -> Declaration {
    d.value = expr(d.value, idents);
    d
}

fn expr(e: Expr, idents: &FxHashMap<IdentId, DeclId>) -> Expr {
    match e {
        Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter().map(|a| fn_arm(a, idents)).collect(),
        ),
        Expr::Identifier {
            info,
            ident_id,
            decl_id: _,
        } => Expr::Identifier {
            info,
            ident_id,
            decl_id: idents.get(&ident_id).copied(),
        },
        Expr::Declaration(d) => {
            Expr::Declaration(Box::new(declaration(*d, idents)))
        }
        Expr::Call(a, b) => Expr::Call(
            Box::new(expr(*a, idents)),
            Box::new(expr(*b, idents)),
        ),
        other => other,
    }
}

fn fn_arm(
    mut arm: FnArm,
    idents: &FxHashMap<IdentId, DeclId>,
) -> FnArm {
    arm.exprs =
        arm.exprs.into_iter().map(|e| expr(e, idents)).collect();
    arm
}
