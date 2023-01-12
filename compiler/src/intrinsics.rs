use crate::ast_step2::types::Type;
use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use parser::Associativity;
use std::fmt::Display;
use strum::EnumIter;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter,
)]
pub enum IntrinsicVariable {
    Minus,
    Plus,
    Percent,
    Multi,
    Lt,
    Neq,
    Eq,
    PrintStr,
    I64ToString,
    Append,
}

impl Display for IntrinsicVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicVariable::Minus => "-",
            IntrinsicVariable::Plus => "+",
            IntrinsicVariable::Percent => "%",
            IntrinsicVariable::Multi => "*",
            IntrinsicVariable::Lt => "<",
            IntrinsicVariable::Neq => "!=",
            IntrinsicVariable::Eq => "==",
            IntrinsicVariable::PrintStr => "print_str",
            IntrinsicVariable::I64ToString => "i64_to_string",
            IntrinsicVariable::Append => "<>",
        }
    }

    pub fn to_type(self) -> Type {
        match self {
            IntrinsicVariable::Minus => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64")
                    .arrow(Type::intrinsic_from_str("I64")),
            ),
            IntrinsicVariable::Plus => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64")
                    .arrow(Type::intrinsic_from_str("I64")),
            ),
            IntrinsicVariable::Percent => Type::intrinsic_from_str("I64")
                .arrow(
                    Type::intrinsic_from_str("I64")
                        .arrow(Type::intrinsic_from_str("I64")),
                ),
            IntrinsicVariable::Multi => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64")
                    .arrow(Type::intrinsic_from_str("I64")),
            ),
            IntrinsicVariable::Lt => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64").arrow(
                    Type::intrinsic_from_str("True")
                        .union(Type::intrinsic_from_str("False")),
                ),
            ),
            IntrinsicVariable::Neq => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64").arrow(
                    Type::intrinsic_from_str("True")
                        .union(Type::intrinsic_from_str("False")),
                ),
            ),
            IntrinsicVariable::Eq => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64").arrow(
                    Type::intrinsic_from_str("True")
                        .union(Type::intrinsic_from_str("False")),
                ),
            ),
            IntrinsicVariable::PrintStr => Type::intrinsic_from_str("String")
                .arrow(Type::intrinsic_from_str("()")),
            IntrinsicVariable::I64ToString => Type::intrinsic_from_str("I64")
                .arrow(Type::intrinsic_from_str("String")),
            IntrinsicVariable::Append => Type::intrinsic_from_str("String")
                .arrow(
                    Type::intrinsic_from_str("String")
                        .arrow(Type::intrinsic_from_str("String")),
                ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicType {
    String,
    I64,
    Unit,
    True,
    False,
    ArgumentTuple,
}

pub static INTRINSIC_TYPES: Lazy<FxHashMap<&'static str, IntrinsicType>> =
    Lazy::new(|| {
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
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter,
)]
pub enum IntrinsicConstructor {
    Unit,
    True,
    False,
}

impl Display for IntrinsicConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
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

    pub fn to_type(self) -> Type {
        match self {
            IntrinsicConstructor::True => Type::intrinsic_from_str("True"),
            IntrinsicConstructor::False => Type::intrinsic_from_str("False"),
            IntrinsicConstructor::Unit => Type::intrinsic_from_str("()"),
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

pub static OP_PRECEDENCE: Lazy<FxHashMap<&'static str, (Associativity, i32)>> =
    Lazy::new(|| {
        use Associativity::*;
        [
            ("%", (Left, 7)),
            ("*", (Left, 7)),
            ("+", (Left, 6)),
            ("-", (Left, 6)),
            ("<", (Left, 5)),
            ("!=", (Left, 5)),
            ("==", (Left, 5)),
            ("<>", (Left, 3)),
            ("|", (Left, 2)),
            ("->", (Right, 1)),
        ]
        .iter()
        .copied()
        .collect()
    });
