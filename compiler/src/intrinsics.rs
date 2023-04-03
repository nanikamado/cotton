use crate::ast_step2::types::Type;
use crate::ast_step2::TypeId;
use crate::ast_step5;
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
    Div,
    Lt,
    Neq,
    Eq,
    PrintStr,
    I64ToString,
    AppendStr,
}

impl Display for IntrinsicVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

const fn runtime_intrinsic_type(i: IntrinsicType) -> ast_step5::TypeUnit {
    ast_step5::TypeUnit::Normal {
        id: TypeId::Intrinsic(i),
        args: Vec::new(),
    }
}

impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicVariable::Minus => "-",
            IntrinsicVariable::Plus => "+",
            IntrinsicVariable::Percent => "%",
            IntrinsicVariable::Multi => "*",
            IntrinsicVariable::Div => "/",
            IntrinsicVariable::Lt => "<",
            IntrinsicVariable::Neq => "!=",
            IntrinsicVariable::Eq => "==",
            IntrinsicVariable::PrintStr => "print_str",
            IntrinsicVariable::I64ToString => "i64_to_string",
            IntrinsicVariable::AppendStr => "append_str",
        }
    }

    pub fn to_type(self) -> Type {
        match self {
            IntrinsicVariable::Minus
            | IntrinsicVariable::Plus
            | IntrinsicVariable::Percent
            | IntrinsicVariable::Multi
            | IntrinsicVariable::Div => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64")
                    .arrow(Type::intrinsic_from_str("I64")),
            ),
            IntrinsicVariable::Lt
            | IntrinsicVariable::Neq
            | IntrinsicVariable::Eq => Type::intrinsic_from_str("I64").arrow(
                Type::intrinsic_from_str("I64").arrow(
                    Type::intrinsic_from_str("True")
                        .union(Type::intrinsic_from_str("False")),
                ),
            ),
            IntrinsicVariable::PrintStr => Type::intrinsic_from_str("String")
                .arrow(Type::intrinsic_from_str("()")),
            IntrinsicVariable::I64ToString => Type::intrinsic_from_str("I64")
                .arrow(Type::intrinsic_from_str("String")),
            IntrinsicVariable::AppendStr => Type::intrinsic_from_str("String")
                .arrow(
                    Type::intrinsic_from_str("String")
                        .arrow(Type::intrinsic_from_str("String")),
                ),
        }
    }

    pub fn parameter_len(self) -> usize {
        match self {
            IntrinsicVariable::Minus
            | IntrinsicVariable::Plus
            | IntrinsicVariable::Percent
            | IntrinsicVariable::Multi
            | IntrinsicVariable::Div
            | IntrinsicVariable::Lt
            | IntrinsicVariable::Neq
            | IntrinsicVariable::Eq
            | IntrinsicVariable::AppendStr => 2,
            IntrinsicVariable::PrintStr | IntrinsicVariable::I64ToString => 1,
        }
    }

    pub fn runtime_return_type(self) -> ast_step5::Type {
        use ast_step5::TypeUnit;
        const I64: TypeUnit = runtime_intrinsic_type(IntrinsicType::I64);
        const TRUE: TypeUnit = runtime_intrinsic_type(IntrinsicType::True);
        const FALSE: TypeUnit = runtime_intrinsic_type(IntrinsicType::False);
        const STRING: TypeUnit = runtime_intrinsic_type(IntrinsicType::String);
        const UNIT: TypeUnit = runtime_intrinsic_type(IntrinsicType::Unit);
        match self {
            IntrinsicVariable::Minus
            | IntrinsicVariable::Plus
            | IntrinsicVariable::Percent
            | IntrinsicVariable::Multi
            | IntrinsicVariable::Div => I64.into(),
            IntrinsicVariable::Lt
            | IntrinsicVariable::Neq
            | IntrinsicVariable::Eq => ast_step5::Type {
                ts: [TRUE, FALSE].into_iter().collect(),
                recursive: false,
                reference: false,
            },
            IntrinsicVariable::PrintStr => UNIT.into(),
            IntrinsicVariable::I64ToString => STRING.into(),
            IntrinsicVariable::AppendStr => STRING.into(),
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
    Fn,
}

impl IntrinsicType {
    pub fn parameter_len(self) -> usize {
        if let Self::Fn = self {
            2
        } else {
            0
        }
    }
}

pub static INTRINSIC_TYPES: Lazy<FxHashMap<&'static str, IntrinsicType>> =
    Lazy::new(|| {
        [
            ("String", IntrinsicType::String),
            ("I64", IntrinsicType::I64),
            ("()", IntrinsicType::Unit),
            ("True", IntrinsicType::True),
            ("False", IntrinsicType::False),
            ("->", IntrinsicType::Fn),
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

    pub fn to_runtime_type(self) -> ast_step5::Type {
        runtime_intrinsic_type(self.into()).into()
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
            ("/", (Left, 7)),
            ("+", (Left, 6)),
            ("-", (Left, 6)),
            ("<", (Left, 5)),
            ("!=", (Left, 5)),
            ("==", (Left, 5)),
            ("|", (Left, 2)),
            ("->", (Right, 1)),
        ]
        .iter()
        .copied()
        .collect()
    });
