use super::Type;
use super::Type::*;
use once_cell::sync::Lazy;
use std::collections::HashMap;

pub static INTRINSIC_VARIABLES: Lazy<HashMap<String, Vec<Type>>> =
    Lazy::new(|| {
        [
            (
                "-",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Fn(
                        Normal("Num".to_string(), Vec::new()).into(),
                        Normal("Num".to_string(), Vec::new()).into(),
                    )
                    .into(),
                )],
            ),
            (
                "+",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Fn(
                        Normal("Num".to_string(), Vec::new()).into(),
                        Normal("Num".to_string(), Vec::new()).into(),
                    )
                    .into(),
                )],
            ),
            (
                "%",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Fn(
                        Normal("Num".to_string(), Vec::new()).into(),
                        Normal("Num".to_string(), Vec::new()).into(),
                    )
                    .into(),
                )],
            ),
            (
                "<",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Fn(
                        Normal("Num".to_string(), Vec::new()).into(),
                        Union(
                            [
                                Normal(
                                    "True".to_string(),
                                    Vec::new(),
                                ),
                                Normal(
                                    "False".to_string(),
                                    Vec::new(),
                                ),
                            ]
                            .iter()
                            .cloned()
                            .collect(),
                        )
                        .into(),
                    )
                    .into(),
                )],
            ),
            (
                "!=",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Fn(
                        Normal("Num".to_string(), Vec::new()).into(),
                        Union(
                            [
                                Normal(
                                    "True".to_string(),
                                    Vec::new(),
                                ),
                                Normal(
                                    "False".to_string(),
                                    Vec::new(),
                                ),
                            ]
                            .iter()
                            .cloned()
                            .collect(),
                        )
                        .into(),
                    )
                    .into(),
                )],
            ),
            (
                "println",
                [Fn(
                    Normal("String".to_string(), Vec::new()).into(),
                    Normal("()".to_string(), Vec::new()).into(),
                )],
            ),
            (
                "num_to_string",
                [Fn(
                    Normal("Num".to_string(), Vec::new()).into(),
                    Normal("String".to_string(), Vec::new()).into(),
                )],
            ),
            ("True", [Normal("True".to_string(), Vec::new())]),
            ("False", [Normal("False".to_string(), Vec::new())]),
        ]
        .map(|(n, t)| (n.to_string(), t.to_vec()))
        .iter()
        .cloned()
        .collect()
    });
