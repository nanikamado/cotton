use crate::ast2::decl_id::{new_decl_id, DeclId};
use crate::ast2::types::Type;
use crate::type_check::type_util::construct_type;
use once_cell::sync::Lazy;
use std::collections::HashMap;

pub static INTRINSIC_VARIABLES: Lazy<
    HashMap<String, Vec<(Type, DeclId)>>,
> = Lazy::new(|| {
    [
        ("-", ["Num -> Num -> Num"]),
        ("+", ["Num -> Num -> Num"]),
        ("%", ["Num -> Num -> Num"]),
        ("<", ["Num -> Num -> True | False"]),
        ("!=", ["Num -> Num -> True | False"]),
        ("println", ["String -> ()"]),
        ("print", ["String -> ()"]),
        ("num_to_string", ["Num -> String"]),
        ("True", ["True"]),
        ("False", ["False"]),
    ]
    .map(|(n, t)| {
        (
            n.to_string(),
            t.map(|s| (construct_type(s), new_decl_id())).to_vec(),
        )
    })
    .iter()
    .cloned()
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
    Arrow,
    Call,
    Bar,
}

pub static INTRINSIC_TYPES: Lazy<HashMap<String, IntrinsicType>> =
    Lazy::new(|| {
        [
            ("String", IntrinsicType::String),
            ("Num", IntrinsicType::Num),
            ("()", IntrinsicType::Unit),
            ("True", IntrinsicType::True),
            ("False", IntrinsicType::False),
            ("->", IntrinsicType::Arrow),
            ("type_call", IntrinsicType::Call),
            ("|", IntrinsicType::Bar),
        ]
        .map(|(n, t)| (n.to_string(), t))
        .iter()
        .cloned()
        .collect()
    });

pub static INTRINSIC_TYPES_NAMES: Lazy<
    HashMap<IntrinsicType, String>,
> = Lazy::new(|| {
    [
        (IntrinsicType::String, "String"),
        (IntrinsicType::Num, "Num"),
        (IntrinsicType::Unit, "()"),
        (IntrinsicType::True, "True"),
        (IntrinsicType::False, "False"),
        (IntrinsicType::Call, "type_call"),
        (IntrinsicType::Arrow, "->"),
        (IntrinsicType::Bar, "|"),
    ]
    .map(|(t, n)| (t, n.to_string()))
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
    pub fn to_str(&self) -> &str {
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
