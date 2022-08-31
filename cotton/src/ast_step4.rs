use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        types::{Type, TypeVariable},
        Pattern, TypeConstructor,
    },
    ast_step3::{self, VariableId},
};
use fxhash::FxHashMap;
use std::collections::BTreeMap;

/// # Difference between `ast_step3::Ast` and `ast_step4::Ast`
/// - Polymorphic variables in `ast_step3::Ast` are replicated and become monomorphic in `ast_step4::Ast`.
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
        /// `Some()` if and only if the ident is a constructor.
        type_args: Option<Vec<Type<'a>>>,
    },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: ExprWithType<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
    pub decl_id: DeclId,
}

impl<'a> From<ast_step3::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step3::Ast<'a>) -> Self {
        let (variable_decl, entry_point) = variable_decl(
            ast.variable_decl,
            &ast.data_decl,
            ast.entry_point,
        );
        let data_decl = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
                field_len: d.fields.len(),
                decl_id: d.decl_id,
            })
            .collect();
        Self {
            variable_decl,
            data_decl,
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

fn variable_decl<'a>(
    variable_decls: Vec<ast_step3::VariableDecl<'a>>,
    data_decls: &[ast_step2::DataDecl<'a>],
    entry_point: DeclId,
) -> (Vec<VariableDecl<'a>>, DeclId) {
    let variable_decls: FxHashMap<DeclId, &ast_step3::VariableDecl> =
        variable_decls
            .iter()
            .map(|d| {
                let did = d.decl_id;
                (did, d)
            })
            .collect();
    let data_decls: FxHashMap<DeclId, &ast_step2::DataDecl<'a>> =
        data_decls
            .iter()
            .map(|d| {
                let did = d.decl_id;
                (did, d)
            })
            .collect();
    log::debug!("decl_decls: {:?}", variable_decls.keys());
    let mut monomorphics = Monomorphics::default();
    let entry_point = monomorphics.get_monomorphic_variables(
        entry_point,
        Default::default(),
        &variable_decls,
        &data_decls,
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
        variable_decls: &FxHashMap<
            DeclId,
            &ast_step3::VariableDecl<'a>,
        >,
        data_decls: &FxHashMap<DeclId, &ast_step2::DataDecl<'a>>,
        mut trace: FxHashMap<DeclId, DeclId>,
    ) -> DeclId {
        if let Some(d) = trace.get(&old_decl_id) {
            *d
        } else if let Some(d) =
            self.0.get(&(old_decl_id, args.clone()))
        {
            d.decl_id
        } else if let Some(d) = variable_decls.get(&old_decl_id) {
            let d = (*d).clone();
            let new_decl_id = DeclId::new();
            trace.insert(old_decl_id, new_decl_id);
            let value = self.monomorphy_expr(
                d.value,
                &args,
                variable_decls,
                data_decls,
                trace,
            );
            verify_types_do_not_have_free_variables(&value)
                .unwrap_or_else(|t| {
                    log::error!(
                        "could not identify type variable in {}, {}",
                        t.1,
                        d.name
                    )
                });
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
        (e, mut t): ast_step3::ExprWithType<'a>,
        args: &BTreeMap<TypeVariable, Type<'a>>,
        variable_decls: &FxHashMap<
            DeclId,
            &ast_step3::VariableDecl<'a>,
        >,
        data_decls: &FxHashMap<DeclId, &ast_step2::DataDecl<'a>>,
        trace: FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType<'a> {
        for (v, to) in args {
            t = t.replace_num(*v, to);
        }
        let e = match e {
            ast_step3::Expr::Lambda(arms) => Expr::Lambda(
                arms.into_iter()
                    .map(|a| {
                        let expr = self.monomorphy_expr(
                            a.expr,
                            args,
                            variable_decls,
                            data_decls,
                            trace.clone(),
                        );
                        FnArm {
                            pattern: a.pattern,
                            expr,
                        }
                    })
                    .collect(),
            ),
            ast_step3::Expr::Number(a) => Expr::Number(a),
            ast_step3::Expr::StrLiteral(a) => Expr::StrLiteral(a),
            ast_step3::Expr::Ident {
                name,
                variable_id,
                type_args,
            } => {
                let mut new_type_args = None;
                let variable_id = match variable_id {
                    VariableId::Decl(decl_id) => {
                        let type_args: BTreeMap<TypeVariable, Type> =
                            type_args
                                .into_iter()
                                .map(|(v, mut t)| {
                                    for (from, to) in args {
                                        t = t.replace_num(*from, to);
                                    }
                                    (v, t)
                                })
                                .collect();
                        if let Some(d) = data_decls.get(&decl_id) {
                            new_type_args = Some(
                                d.fields
                                    .iter()
                                    .map(|v| type_args[v].clone())
                                    .collect(),
                            );
                            VariableId::Decl(decl_id)
                        } else {
                            VariableId::Decl(
                                self.get_monomorphic_variables(
                                    decl_id,
                                    type_args,
                                    variable_decls,
                                    data_decls,
                                    trace,
                                ),
                            )
                        }
                    }
                    a => a,
                };
                Expr::Ident {
                    name,
                    variable_id,
                    type_args: new_type_args,
                }
            }
            ast_step3::Expr::Call(f, a) => Expr::Call(
                self.monomorphy_expr(
                    *f,
                    args,
                    variable_decls,
                    data_decls,
                    trace.clone(),
                )
                .into(),
                self.monomorphy_expr(
                    *a,
                    args,
                    variable_decls,
                    data_decls,
                    trace,
                )
                .into(),
            ),
            ast_step3::Expr::Do(exprs) => Expr::DoBlock(
                exprs
                    .into_iter()
                    .map(|expr| {
                        self.monomorphy_expr(
                            expr,
                            args,
                            variable_decls,
                            data_decls,
                            trace.clone(),
                        )
                    })
                    .collect(),
            ),
        };
        (e, t)
    }
}

fn verify_types_do_not_have_free_variables<'a, 'b>(
    et: &'b ExprWithType<'a>,
) -> Result<(), &'b ExprWithType<'a>> {
    if et.1.all_type_variables().is_empty() {
        match &et.0 {
            Expr::Lambda(arms) => arms.iter().try_for_each(|arm| {
                verify_types_do_not_have_free_variables(&arm.expr)
            }),
            Expr::Number(_)
            | Expr::StrLiteral(_)
            | Expr::Ident { .. } => Ok(()),
            Expr::Call(e1, e2) => [e1, e2].iter().try_for_each(|e| {
                verify_types_do_not_have_free_variables(e)
            }),
            Expr::DoBlock(es) => es.iter().try_for_each(
                verify_types_do_not_have_free_variables,
            ),
        }
    } else {
        Err(et)
    }
}
