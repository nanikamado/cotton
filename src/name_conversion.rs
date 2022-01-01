use crate::{
    ast0::DataDeclaration,
    ast1::{ident_id::IdentId, Ast, Declaration, Expr, FnArm},
};
use fxhash::FxHashMap;
use hashbag::HashBag;

pub fn run(mut ast: Ast, idents: &FxHashMap<IdentId, usize>) -> Ast {
    let mut toplevel_name_count = HashBag::<String>::new();
    ast.declarations = ast
        .declarations
        .into_iter()
        .map(|d| declaration(d, idents, &mut toplevel_name_count))
        .collect();
    ast.data_declarations = ast
        .data_declarations
        .into_iter()
        .map(|d| data_declaration(d, &mut toplevel_name_count))
        .collect();
    ast
}

fn declaration(
    mut d: Declaration,
    idents: &FxHashMap<IdentId, usize>,
    toplevel_name_count: &mut HashBag<String>,
) -> Declaration {
    let count = toplevel_name_count.insert(d.identifier.clone());
    d.identifier += &format!("${}", count);
    d.value = expr(d.value, idents, toplevel_name_count);
    d
}

fn expr(
    e: Expr,
    idents: &FxHashMap<IdentId, usize>,
    toplevel_name_count: &mut HashBag<String>,
) -> Expr {
    match e {
        Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter()
                .map(|a| fn_arm(a, idents, toplevel_name_count))
                .collect(),
        ),
        Expr::Identifier(name, id) => Expr::Identifier(
            if let Some(n) = idents.get(&id) {
                format!("{}${}", name, n)
            } else {
                name
            },
            id,
        ),
        Expr::Declaration(d) => Expr::Declaration(Box::new(
            declaration(*d, idents, toplevel_name_count),
        )),
        Expr::Call(a, b) => Expr::Call(
            Box::new(expr(*a, idents, toplevel_name_count)),
            Box::new(expr(*b, idents, toplevel_name_count)),
        ),
        other => other,
    }
}

fn fn_arm(
    mut arm: FnArm,
    idents: &FxHashMap<IdentId, usize>,
    toplevel_name_count: &mut HashBag<String>,
) -> FnArm {
    arm.exprs = arm
        .exprs
        .into_iter()
        .map(|e| expr(e, idents, toplevel_name_count))
        .collect();
    arm
}

fn data_declaration(
    mut d: DataDeclaration,
    toplevel_name_count: &mut HashBag<String>,
) -> DataDeclaration {
    let count = toplevel_name_count.insert(d.name.clone());
    d.name += &format!("${}", count);
    d
}
