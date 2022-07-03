use crate::{
    ast_step2::types::Type, ast_step3::type_util::construct_type,
    parse::Associativity,
};
use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use std::fmt::Display;
use strum::EnumIter;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter,
)]
pub enum IntrinsicVariable {
    Minus,
    Plus,
    Percent,
    Lt,
    Neq,
    Println,
    Print,
    I64ToString,
    True,
    False,
    Unit,
}

impl Display for IntrinsicVariable {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicVariable::Minus => "-",
            IntrinsicVariable::Plus => "+",
            IntrinsicVariable::Percent => "%",
            IntrinsicVariable::Lt => "<",
            IntrinsicVariable::Neq => "!=",
            IntrinsicVariable::Println => "println",
            IntrinsicVariable::Print => "print",
            IntrinsicVariable::I64ToString => "i64_to_string",
            IntrinsicVariable::True => "True",
            IntrinsicVariable::False => "False",
            IntrinsicVariable::Unit => "()",
        }
    }

    pub fn to_type(self) -> &'static Type<'static> {
        &INTRINSIC_VARIABLES_TYPES[&self]
    }
}

pub static INTRINSIC_VARIABLES_TYPES: Lazy<
    FxHashMap<IntrinsicVariable, Type>,
> = Lazy::new(|| {
    [
        (IntrinsicVariable::Minus, "I64 -> I64 -> I64"),
        (IntrinsicVariable::Plus, "I64 -> I64 -> I64"),
        (IntrinsicVariable::Percent, "I64 -> I64 -> I64"),
        (IntrinsicVariable::Lt, "I64 -> I64 -> True | False"),
        (IntrinsicVariable::Neq, "I64 -> I64 -> True | False"),
        (IntrinsicVariable::Println, "String -> ()"),
        (IntrinsicVariable::Print, "String -> ()"),
        (IntrinsicVariable::I64ToString, "I64 -> String"),
        (IntrinsicVariable::True, "True"),
        (IntrinsicVariable::False, "False"),
        (IntrinsicVariable::Unit, "()"),
    ]
    .iter()
    .map(|(n, t)| (*n, construct_type(t)))
    .collect()
});

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum IntrinsicType {
    String,
    I64,
    Unit,
    True,
    False,
}

pub static INTRINSIC_TYPES: Lazy<
    FxHashMap<&'static str, IntrinsicType>,
> = Lazy::new(|| {
    [
        ("String", IntrinsicType::String),
        ("I64", IntrinsicType::I64),
        ("()", IntrinsicType::Unit),
        ("True", IntrinsicType::True),
        ("False", IntrinsicType::False),
    ]
    .map(|(n, t)| (n, t))
    .iter()
    .cloned()
    .collect()
});

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum IntrinsicConstructor {
    Unit,
    True,
    False,
}

pub static INTRINSIC_CONSTRUCTORS: Lazy<
    FxHashMap<String, IntrinsicConstructor>,
> = Lazy::new(|| {
    [
        ("()", IntrinsicConstructor::Unit),
        ("True", IntrinsicConstructor::True),
        ("False", IntrinsicConstructor::False),
    ]
    .map(|(n, t)| (n.to_string(), t))
    .iter()
    .cloned()
    .collect()
});

impl IntrinsicConstructor {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicConstructor::Unit => "()",
            IntrinsicConstructor::True => "True",
            IntrinsicConstructor::False => "False",
        }
    }
}

impl From<IntrinsicConstructor> for IntrinsicType {
    fn from(c: IntrinsicConstructor) -> Self {
        match c {
            IntrinsicConstructor::Unit => Self::Unit,
            IntrinsicConstructor::True => Self::True,
            IntrinsicConstructor::False => Self::False,
        }
    }
}

pub static OP_PRECEDENCE: Lazy<
    FxHashMap<&'static str, (Associativity, i32)>,
> = Lazy::new(|| {
    use Associativity::*;
    [
        ("%", (Left, 7)),
        ("+", (Left, 6)),
        ("-", (Left, 6)),
        ("<", (Left, 5)),
        ("!=", (Left, 5)),
        ("|", (Left, 2)),
        ("->", (Right, 1)),
    ]
    .iter()
    .copied()
    .collect()
});
