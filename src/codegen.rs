use crate::ast2::{Declaration, Expr, AST};
use escodegen::Stmt;

pub fn compile(ast: AST) -> Stmt {
    Stmt::Block(
        ast.declarations.into_iter().map(declaration).collect(),
    )
}

fn declaration(d: Declaration) -> Stmt {
    Stmt::Var(d.identifier, Some(expr(d.value)))
}

fn expr(_e: Expr) -> escodegen::Expr {
    todo!()
}
