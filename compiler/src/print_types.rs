use crate::ast_step3::{Ast, VariableId};

pub fn print(ast: &Ast) {
    for d in &ast.variable_decl {
        println!(
            "{} : {}",
            d.name,
            &ast.types_of_global_decls[&VariableId::Decl(d.decl_id)].t
        );
    }
}
