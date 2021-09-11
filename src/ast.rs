#[derive(Debug, PartialEq, Eq)]
pub struct AST {
    pub declarations: Vec<Declaration>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Datatype,
    pub value: OpSequence,
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

impl Into<OpSequence> for Expr {
    fn into(self) -> OpSequence {
        OpSequence {
            operators: Vec::new(),
            operands: vec![Operand::Expr(self)],
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct OpSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Operand>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operand {
    Expr(Expr),
    FnCallArguments(Vec<OpSequence>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FnArm {
    pub pattern: Pattern,
    pub exprs: Vec<OpSequence>,
}

pub type Pattern = String;
