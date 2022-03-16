#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub decls: Vec<Decl>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    Variable(VariableDecl),
    Data(DataDecl),
    Precedence(OperatorPrecedence),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub identifier: String,
    pub type_annotation: Option<(InfixTypeSequence, Forall)>,
    pub value: OpSequence,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Identifier(String),
    Paren(InfixTypeSequence),
}

pub type InfixTypeSequence = Vec<OpSequenceUnit<Type>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<T> {
    Operand(T),
    Operator(String),
    Apply(T),
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Forall {
    pub type_variable_names: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: String,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Identifier(String),
    Decl(Box<VariableDecl>),
    Unit,
    Paren(OpSequence),
}

pub type OpSequence = Vec<OpSequenceUnit<Expr>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<InfixConstructorSequence>,
    pub pattern_type: Vec<Option<InfixTypeSequence>>,
    pub exprs: Vec<OpSequence>,
}

pub type InfixConstructorSequence = Vec<OpSequenceUnit<Pattern>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Number(String),
    StrLiteral(String),
    Constructor(String, Vec<Pattern>),
    Binder(String),
    Underscore,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OperatorPrecedence {
    pub name: String,
    pub associativity: Associativity,
    pub precedence: i32,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Associativity {
    Left,
    Right,
    UnaryLeft,
}
