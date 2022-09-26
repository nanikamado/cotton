use crate::{
    ast_step2::IncompleteType,
    ast_step3::{Ast, VariableId},
};
use itertools::Itertools;
use std::fmt::Display;

pub fn print(ast: &Ast<'_>) {
    for d in &ast.variable_decl {
        println!(
            "{} : {}",
            d.name,
            FormatForTest(&ast.types_of_decls[&VariableId::Decl(d.decl_id)])
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
