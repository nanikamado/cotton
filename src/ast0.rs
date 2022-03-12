#[derive(Debug, PartialEq, Eq)]
pub struct Ast {
    pub decls: Vec<Decl>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    Variable(VariableDecl),
    Data(DataDecl),
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InfixTypeSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Type>,
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpSequence {
    pub operators: Vec<String>,
    pub operands: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<InfixConstructorSequence>,
    pub pattern_type: Vec<Option<InfixTypeSequence>>,
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
