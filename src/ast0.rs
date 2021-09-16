#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub declarations: Vec<Dec>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Dec {
    Variable(Declaration),
    Data(DataDeclaration),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Declaration {
    pub identifier: String,
    pub datatype: Datatype,
    pub value: OpSequence,
}

pub type Datatype = ();

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDeclaration {
    pub name: String,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Declaration(Box<Declaration>),
    Unit,
    Paren(OpSequence),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Expr>,
}

impl From<Expr> for OpSequence {
    fn from(e: Expr) -> Self {
        OpSequence {
            operators: Vec::new(),
            operands: vec![e],
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<InfixConstructorSequence>,
    pub exprs: Vec<OpSequence>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InfixConstructorSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Pattern>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(String),
    StrLiteral(String),
    Constructor(String, Vec<Pattern>),
    Binder(String),
    Underscore,
}