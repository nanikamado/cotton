use std::fmt::Display;

use crate::ast_step2::{decl_id::DeclId, types::Type, Ast, IncompleteType};
use fxhash::FxHashMap;
use itertools::Itertools;

#[allow(unused)]
pub fn print<'a>(
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a, Type<'a>>>,
    ast: Ast<'a>,
) {
    for d in ast.variable_decl {
        println!(
            "{} : {}",
            d.name,
            FormatForTest(&types_of_decls[&d.decl_id])
        );
    }
}

struct FormatForTest<'a, 'b>(&'a IncompleteType<'b>);

impl Display for FormatForTest<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} forall {{\n{}}}",
            self.0.constructor,
            self.0.subtype_relations.0.iter().format_with("", |a, f| f(
                &format_args!("{} < {}\n", a.0, a.1)
            ))
        )
    }
}
