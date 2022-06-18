use std::collections::BTreeMap;

use crate::{
    ast_level2::{
        decl_id::{new_decl_id, DeclId},
        types::{Type, TypeVariable},
        DataDecl, Pattern, TypeConstructor,
    },
    ast_level3::{self, VariableId},
};
use fxhash::FxHashMap;

/// # Difference between `ast_level2::Ast` and `ast_level3::Ast`
/// - The names of variables are resolved.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, Type<'a>);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: &'a str,
        variable_id: VariableId,
    },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: ExprWithType<'a>,
}

impl<'a> From<ast_level3::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_level3::Ast<'a>) -> Self {
        let (variable_decl, entry_point) =
            variable_decl(ast.variable_decl, ast.entry_point);
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point,
        }
    }
}

#[derive(Debug, PartialEq, Clone, Default)]
struct Monomorphics<'a>(
    FxHashMap<
        (DeclId, BTreeMap<TypeVariable, Type<'a>>),
        VariableDecl<'a>,
    >,
);

fn variable_decl(
    decls: Vec<ast_level3::VariableDecl>,
    entry_point: DeclId,
) -> (Vec<VariableDecl>, DeclId) {
    let decl_map: FxHashMap<DeclId, &ast_level3::VariableDecl> =
        decls
            .iter()
            .map(|d| {
                let did = d.decl_id;
                (did, d)
            })
            .collect();
    log::debug!("decl_map: {:?}", decl_map.keys());
    let mut monomorphics = Monomorphics::default();
    let entry_point = monomorphics.get_monomorphic_variables(
        entry_point,
        Default::default(),
        &decl_map,
        Default::default(),
    );
    let decls = monomorphics.0.into_iter().map(|(_, d)| d).collect();
    (decls, entry_point)
}

impl<'a> Monomorphics<'a> {
    fn get_monomorphic_variables(
        &mut self,
        old_decl_id: DeclId,
        args: BTreeMap<TypeVariable, Type<'a>>,
        decl_map: &FxHashMap<DeclId, &ast_level3::VariableDecl<'a>>,
        mut trace: FxHashMap<DeclId, DeclId>,
    ) -> DeclId {
        if let Some(d) = trace.get(&old_decl_id) {
            *d
        } else if let Some(d) =
            self.0.get(&(old_decl_id, args.clone()))
        {
            d.decl_id
        } else if let Some(d) = decl_map.get(&old_decl_id) {
            let d = (*d).clone();
            let new_decl_id = new_decl_id();
            trace.insert(old_decl_id, new_decl_id);
            let value =
                self.monomorphy_expr(d.value, &args, decl_map, trace);
            self.0.insert(
                (old_decl_id, args),
                VariableDecl {
                    name: d.name,
                    value,
                    decl_id: new_decl_id,
                },
            );
            new_decl_id
        } else {
            old_decl_id
        }
    }

    fn monomorphy_expr(
        &mut self,
        (e, mut t): ast_level3::ExprWithType<'a>,
        args: &BTreeMap<TypeVariable, Type<'a>>,
        decl_map: &FxHashMap<DeclId, &ast_level3::VariableDecl<'a>>,
        trace: FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType<'a> {
        for (v, to) in args {
            t = t.replace_num(*v, to);
        }
        let e = match e {
            ast_level3::Expr::Lambda(arms) => Expr::Lambda(
                arms.into_iter()
                    .map(|a| {
                        let expr = self.monomorphy_expr(
                            a.expr,
                            args,
                            decl_map,
                            trace.clone(),
                        );
                        FnArm {
                            pattern: a.pattern,
                            expr,
                        }
                    })
                    .collect(),
            ),
            ast_level3::Expr::Number(a) => Expr::Number(a),
            ast_level3::Expr::StrLiteral(a) => Expr::StrLiteral(a),
            ast_level3::Expr::Ident {
                name,
                variable_id,
                type_args,
            } => {
                let variable_id = match variable_id {
                    VariableId::Decl(decl_id) => VariableId::Decl(
                        self.get_monomorphic_variables(
                            decl_id,
                            type_args
                                .into_iter()
                                .map(|(v, mut t)| {
                                    for (from, to) in args {
                                        t = t.replace_num(*from, to);
                                    }
                                    (v, t)
                                })
                                .collect(),
                            decl_map,
                            trace,
                        ),
                    ),
                    a => a,
                };
                Expr::Ident { name, variable_id }
            }
            ast_level3::Expr::Decl(_) => unimplemented!(),
            ast_level3::Expr::Call(f, a) => Expr::Call(
                self.monomorphy_expr(
                    *f,
                    args,
                    decl_map,
                    trace.clone(),
                )
                .into(),
                self.monomorphy_expr(*a, args, decl_map, trace)
                    .into(),
            ),
            ast_level3::Expr::DoBlock(exprs) => Expr::DoBlock(
                exprs
                    .into_iter()
                    .map(|expr| {
                        self.monomorphy_expr(
                            expr,
                            args,
                            decl_map,
                            trace.clone(),
                        )
                    })
                    .collect(),
            ),
        };
        (e, t)
    }
}
