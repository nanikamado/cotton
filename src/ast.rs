#[derive(Debug, PartialEq, Eq)]
pub struct AST {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Datatype,
    pub value: OpExpr,
}

pub type Datatype = ();

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<Declaration>),
    Unit,
}

impl Into<OpExpr> for Expr {
    fn into(self) -> OpExpr {
        OpExpr {
            operators: Vec::new(),
            operands: vec![Operand::Expr(self)],
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct OpExpr {
    pub operators: Vec<String>,
    pub operands: Vec<Operand>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operand {
    Expr(Expr),
    FnCallArguments(Vec<OpExpr>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FnArm {
    pub pattern: Pattern,
    pub exprs: Vec<OpExpr>,
}

pub type Pattern = String;
