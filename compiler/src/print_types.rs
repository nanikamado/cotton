use crate::{
    ast_step2::TypeWithEnv,
    ast_step3::{Ast, VariableId},
};
use itertools::Itertools;
use std::fmt::Display;

pub fn print(ast: &Ast) {
    for d in &ast.variable_decl {
        println!(
            "{} : {}",
            d.name,
            FormatForTest(
                &ast.types_of_global_decls[&VariableId::Decl(d.decl_id)]
                    .type_with_env
            )
        );
    }
}

struct FormatForTest<'a>(&'a TypeWithEnv);

impl Display for FormatForTest<'_> {
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
