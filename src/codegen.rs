use crate::ast::{Declaration, OpSequence, AST};
use escodegen::Stmt;

pub fn compile(ast: AST) -> Stmt {
    Stmt::Block(
        ast.declarations.into_iter().map(declaration).collect(),
    )
}

fn declaration(d: Declaration) -> Stmt {
    Stmt::Var(d.identifier, Some(op_expr(d.value)))
}

fn op_expr(_e: OpSequence) -> escodegen::Expr {
    todo!()
}
