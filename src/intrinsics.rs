use crate::{
    ast_level0::Associativity, ast_level2::types::Type,
    ast_level3::type_util::construct_type,
};
use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use std::{collections::HashMap, fmt::Display};
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
    NumToString,
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
            IntrinsicVariable::NumToString => "num_to_string",
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
    HashMap<IntrinsicVariable, Type>,
> = Lazy::new(|| {
    [
        (IntrinsicVariable::Minus, "Num -> Num -> Num"),
        (IntrinsicVariable::Plus, "Num -> Num -> Num"),
        (IntrinsicVariable::Percent, "Num -> Num -> Num"),
        (IntrinsicVariable::Lt, "Num -> Num -> True | False"),
        (IntrinsicVariable::Neq, "Num -> Num -> True | False"),
        (IntrinsicVariable::Println, "String -> ()"),
        (IntrinsicVariable::Print, "String -> ()"),
        (IntrinsicVariable::NumToString, "Num -> String"),
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
    Num,
    Unit,
    True,
    False,
}

pub static INTRINSIC_TYPES: Lazy<
    HashMap<&'static str, IntrinsicType>,
> = Lazy::new(|| {
    [
        ("String", IntrinsicType::String),
        ("Num", IntrinsicType::Num),
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
    HashMap<String, IntrinsicConstructor>,
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
