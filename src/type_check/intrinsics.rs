use crate::ast1::Type;
use crate::type_check::type_util::construct_type;
use once_cell::sync::Lazy;
use std::collections::HashMap;

pub static INTRINSIC_VARIABLES: Lazy<HashMap<String, Vec<Type>>> =
    Lazy::new(|| {
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
        .map(|(n, t)| (n.to_string(), t.map(construct_type).to_vec()))
        .iter()
        .cloned()
        .collect()
    });
