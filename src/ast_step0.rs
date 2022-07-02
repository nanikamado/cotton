#[derive(Debug, PartialEq, Eq)]
pub struct Ast<'a> {
    pub decls: Vec<Decl<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl<'a> {
    Variable(VariableDecl<'a>),
    Data(DataDecl<'a>),
    Precedence(OpPrecedenceDecl<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_annotation: Option<(Type<'a>, Forall<'a>)>,
    pub value: Expr<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeUnit<'a> {
    Ident(&'a str),
    Paren(Type<'a>),
}

pub type Type<'a> = Vec<OpSequenceUnit<'a, TypeUnit<'a>>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OpSequenceUnit<'a, T> {
    Operand(T),
    Operator(&'a str),
    Apply(T),
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Forall<'a> {
    pub type_variables: Vec<&'a str>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExprUnit<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident(&'a str),
    Decl(Box<VariableDecl<'a>>),
    Paren(Expr<'a>),
}

pub type Expr<'a> = Vec<OpSequenceUnit<'a, ExprUnit<'a>>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub exprs: Vec<Expr<'a>>,
}

pub type Pattern<'a> = Vec<OpSequenceUnit<'a, PatternUnit<'a>>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<'a> {
    Number(&'a str),
    StrLiteral(&'a str),
    Constructor(&'a str, Vec<PatternUnit<'a>>),
    Binder(&'a str),
    Underscore,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OpPrecedenceDecl<'a> {
    pub name: &'a str,
    pub associativity: Associativity,
    pub precedence: i32,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Associativity {
    Left,
    Right,
    UnaryLeft,
}
