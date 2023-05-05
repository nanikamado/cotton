use crate::ast_step2::types::Type;
use crate::intrinsics::{IntrinsicConstructor, IntrinsicVariable};

impl IntrinsicConstructor {
    pub fn to_type(self) -> Type {
        match self {
            IntrinsicConstructor::True => Type::intrinsic_from_str("True"),
            IntrinsicConstructor::False => Type::intrinsic_from_str("False"),
            IntrinsicConstructor::Unit => Type::intrinsic_from_str("()"),
        }
    }
}

impl IntrinsicVariable {
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
}