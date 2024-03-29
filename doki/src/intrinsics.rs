use crate::{ast_step1, ast_step2};
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
    Multi,
    Div,
    Lt,
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

const fn runtime_intrinsic_type(i: IntrinsicType) -> ast_step2::TypeUnit {
    ast_step2::TypeUnit::Normal {
        id: ast_step1::TypeId::Intrinsic(i),
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
            IntrinsicVariable::Lt => "lt",
            IntrinsicVariable::Eq => "eq",
            IntrinsicVariable::PrintStr => "print_str",
            IntrinsicVariable::I64ToString => "i64_to_string",
            IntrinsicVariable::AppendStr => "append_str",
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
            | IntrinsicVariable::Eq
            | IntrinsicVariable::AppendStr => 2,
            IntrinsicVariable::PrintStr | IntrinsicVariable::I64ToString => 1,
        }
    }

    pub fn runtime_return_type(self) -> IntrinsicType {
        use IntrinsicType::*;
        match self {
            IntrinsicVariable::Minus
            | IntrinsicVariable::Plus
            | IntrinsicVariable::Percent
            | IntrinsicVariable::Multi
            | IntrinsicVariable::Div => I64,
            IntrinsicVariable::Lt | IntrinsicVariable::Eq => I64,
            IntrinsicVariable::PrintStr => Unit,
            IntrinsicVariable::I64ToString => String,
            IntrinsicVariable::AppendStr => String,
        }
    }

    pub fn runtime_arg_type_id(self) -> Vec<ast_step1::TypeId> {
        use ast_step1::TypeId;
        const I64: TypeId = TypeId::Intrinsic(IntrinsicType::I64);
        const STRING: TypeId = TypeId::Intrinsic(IntrinsicType::String);
        match self {
            IntrinsicVariable::Minus
            | IntrinsicVariable::Plus
            | IntrinsicVariable::Percent
            | IntrinsicVariable::Multi
            | IntrinsicVariable::Div
            | IntrinsicVariable::Lt
            | IntrinsicVariable::Eq => vec![I64, I64],
            IntrinsicVariable::PrintStr => vec![STRING],
            IntrinsicVariable::I64ToString => vec![I64],
            IntrinsicVariable::AppendStr => vec![STRING, STRING],
        }
    }

    pub fn runtime_arg_type(self) -> Vec<ast_step2::Type> {
        self.runtime_arg_type_id()
            .into_iter()
            .map(|id| {
                ast_step2::TypeUnit::Normal {
                    id,
                    args: Vec::new(),
                }
                .into()
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicType {
    String,
    I64,
    Unit,
    True,
    False,
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

    pub fn to_runtime_type(self) -> ast_step2::Type {
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
