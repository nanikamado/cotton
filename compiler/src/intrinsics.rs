use crate::ast_step2::types::Type;
use doki::intrinsics::{IntrinsicConstructor, IntrinsicVariable};
use fxhash::FxHashMap;
use once_cell::sync::Lazy;
use parser::Associativity;

pub fn constructor_type(id: IntrinsicConstructor) -> Type {
    match id {
        IntrinsicConstructor::True => Type::intrinsic_from_str("True"),
        IntrinsicConstructor::False => Type::intrinsic_from_str("False"),
        IntrinsicConstructor::Unit => Type::intrinsic_from_str("()"),
    }
}

pub fn variable_type(id: IntrinsicVariable) -> Type {
    match id {
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
