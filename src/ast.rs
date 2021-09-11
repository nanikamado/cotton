#[derive(Debug, PartialEq, Eq)]
pub struct AST {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Datatype,
    pub value: OpSequence,
}

pub type Datatype = ();

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<Declaration>),
    Unit,
    Parenthesized(Box<OpSequence>),
}

impl Into<OpSequence> for Expr {
    fn into(self) -> OpSequence {
        OpSequence {
            operators: Vec::new(),
            operands: vec![self],
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Pattern,
    pub exprs: Vec<OpSequence>,
}

pub type Pattern = String;
