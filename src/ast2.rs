use crate::ast;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub struct AST {
    pub declarations: Vec<Declaration>,
    pub data_declarations: Vec<ast::DataDeclaration>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Datatype,
    pub value: Expr,
}

impl From<ast::Declaration> for Declaration {
    fn from(d: ast::Declaration) -> Self {
        Self {
            identifier: d.identifier,
            datatype: d.datatype,
            value: d.value.into(),
        }
    }
}

pub type Datatype = ();

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<Declaration>),
    Call(Box<Expr>, Box<Expr>),
    Unit,
}

impl From<ast::Expr> for Expr {
    fn from(ast_expr: ast::Expr) -> Self {
        use Expr::*;
        match ast_expr {
            ast::Expr::Lambda(a) => {
                Lambda(a.into_iter().map(|f| f.into()).collect())
            }
            ast::Expr::Number(a) => Number(a),
            ast::Expr::StrLiteral(a) => StrLiteral(a),
            ast::Expr::Identifier(a) => Identifier(a),
            ast::Expr::Declaration(a) => {
                Declaration(Box::new((*a).into()))
            }
            ast::Expr::Unit => Unit,
            ast::Expr::Parenthesized(a) => (*a).into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<ast::Pattern>,
    pub exprs: Vec<Expr>,
}

impl From<ast::FnArm> for FnArm {
    fn from(ast_fn_arm: ast::FnArm) -> Self {
        Self {
            pattern: ast_fn_arm.pattern,
            exprs: ast_fn_arm
                .exprs
                .into_iter()
                .map(Expr::from)
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Operator(String);

static OP_PRECEDENCE: Lazy<HashMap<&str, i32>> = Lazy::new(|| {
    [("fn_call", 10), (".", 10), ("+", 6), ("-", 6)]
        .iter()
        .cloned()
        .collect()
});

impl Ord for Operator {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        OP_PRECEDENCE[&self.0[..]].cmp(&OP_PRECEDENCE[&other.0[..]])
    }
}

impl PartialOrd for Operator {
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl From<ast::AST> for AST {
    fn from(ast: ast::AST) -> Self {
        let (vs, ds) = ast
            .declarations
            .into_iter()
            .map(|d| match d {
                ast::Dec::Variable(a) => Ok(declaration(a)),
                ast::Dec::Data(a) => Err(a),
            })
            .partition_result();
        AST {
            declarations: vs,
            data_declarations: ds,
        }
    }
}

fn declaration(d: ast::Declaration) -> Declaration {
    Declaration {
        identifier: d.identifier,
        datatype: d.datatype,
        value: d.value.into(),
    }
}

impl From<ast::OpSequence> for Expr {
    fn from(s: ast::OpSequence) -> Self {
        let mut op_list: Vec<_> = s
            .operators
            .clone()
            .into_iter()
            .map(|s| Operator(s))
            .collect();
        op_list.sort();
        op_list.dedup();
        let mut operators = s.operators;
        let mut operands: Vec<Expr> =
            s.operands.into_iter().map(|o| o.into()).collect();
        for a in op_list.into_iter().rev() {
            let mut operand_head = 0;
            for i in 0..operators.len() {
                let op = operators[i].clone();
                if a.0 == op {
                    operands[operand_head] = Expr::Call(
                        Box::new(if op == *"fn_call" {
                            operands[operand_head].clone()
                        } else {
                            Expr::Call(
                                Box::new(Expr::Identifier(op)),
                                Box::new(
                                    operands[operand_head].clone(),
                                ),
                            )
                        }),
                        Box::new(operands[i + 1].clone()),
                    );
                } else {
                    operand_head += 1;
                    operands[operand_head] = operands[i + 1].clone();
                }
            }
            operators.retain(|o| *o != a.0);
        }
        operands[0].clone()
    }
}
