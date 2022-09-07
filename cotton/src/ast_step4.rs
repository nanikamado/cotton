use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        types::{Type, TypeUnit, TypeVariable},
        Pattern, PatternUnit, TypeConstructor,
    },
    ast_step3::{self, ResolvedIdent, ResolvedIdents, VariableId},
};
use fxhash::FxHashMap;
use std::collections::{BTreeMap, BTreeSet};

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
            &ast.resolved_idents,
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

#[derive(Debug, PartialEq, Clone)]
struct Monomorphics<'a, 'b> {
    map: FxHashMap<
        (DeclId, BTreeMap<TypeVariable, Type<'a>>),
        VariableDecl<'a>,
    >,
    variable_decls:
        FxHashMap<DeclId, &'b ast_step3::VariableDecl<'a>>,
    data_decls: FxHashMap<DeclId, &'b ast_step2::DataDecl<'a>>,
    resolved_idents: &'b ResolvedIdents<'a>,
}

fn variable_decl<'a>(
    variable_decls: Vec<ast_step3::VariableDecl<'a>>,
    data_decls: &[ast_step2::DataDecl<'a>],
    entry_point: DeclId,
    resolved_idents: &ResolvedIdents<'a>,
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
    let mut monomorphics = Monomorphics {
        map: Default::default(),
        variable_decls,
        data_decls,
        resolved_idents,
    };
    let entry_point = monomorphics.get_monomorphic_variables(
        entry_point,
        Default::default(),
        Default::default(),
        Default::default(),
    );
    let decls =
        monomorphics.map.into_iter().map(|(_, d)| d).collect();
    (decls, entry_point)
}

impl<'a> Monomorphics<'a, '_> {
    fn get_monomorphic_variables(
        &mut self,
        old_decl_id: DeclId,
        type_args: BTreeMap<TypeVariable, Type<'a>>,
        implicit_args: BTreeSet<(DeclId, &'a str, Type<'a>)>,
        mut trace: FxHashMap<DeclId, DeclId>,
    ) -> DeclId {
        if let Some(d) = trace.get(&old_decl_id) {
            *d
        } else if let Some(d) =
            self.map.get(&(old_decl_id, type_args.clone()))
        {
            d.decl_id
        } else if let Some(d) = self.variable_decls.get(&old_decl_id)
        {
            let d = (*d).clone();
            let new_decl_id = DeclId::new();
            trace.insert(old_decl_id, new_decl_id);
            let (mut value, mut value_t) =
                self.monomorphy_expr(d.value, &type_args, trace);
            for (decl_id, name, t) in implicit_args.into_iter().rev()
            {
                value = Expr::Lambda(vec![FnArm {
                    pattern: vec![vec![PatternUnit::Binder(
                        name, decl_id,
                    )]],
                    expr: (value, value_t.clone()),
                }]);
                value_t = TypeUnit::Fn(t, value_t).into();
            }
            let value = (value, value_t);
            verify_types_do_not_have_free_variables(&value)
                .unwrap_or_else(|t| {
                    panic!(
                        "could not identify type variable in {}, {}",
                        t.1, d.name
                    )
                });
            self.map.insert(
                (old_decl_id, type_args),
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

    fn get_variable_id_from_resolved_item(
        &mut self,
        resolved_item: &ResolvedIdent<'a>,
        trace: FxHashMap<DeclId, DeclId>,
    ) -> (VariableId, Option<Vec<Type<'a>>>) {
        let mut new_type_args = None;
        let type_args: BTreeMap<_, _> = resolved_item
            .type_args
            .iter()
            .map(|(v, t)| (*v, t.clone()))
            .collect();
        let variable_id = match resolved_item.variable_id {
            VariableId::Decl(decl_id) => {
                if let Some(d) = self.data_decls.get(&decl_id) {
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
                            resolved_item
                                .implicit_args
                                .iter()
                                .map(|(i, name, t, _)| {
                                    (*i, *name, t.clone())
                                })
                                .collect(),
                            trace,
                        ),
                    )
                }
            }
            a => a,
        };
        (variable_id, new_type_args)
    }

    fn monomorphy_expr(
        &mut self,
        (e, mut t): ast_step3::ExprWithType<'a>,
        t_args: &BTreeMap<TypeVariable, Type<'a>>,
        trace: FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType<'a> {
        for (v, to) in t_args {
            t = t.replace_num(*v, to);
        }
        let e = match e {
            ast_step3::Expr::Lambda(arms) => Expr::Lambda(
                arms.into_iter()
                    .map(|a| {
                        let expr = self.monomorphy_expr(
                            a.expr,
                            t_args,
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
            ast_step3::Expr::Ident { name, ident_id } => {
                let resolved_item = self
                    .resolved_idents
                    .get(&ident_id)
                    .unwrap()
                    .clone()
                    .replace_variables(t_args);
                let (variable_id, new_type_args) = self
                    .get_variable_id_from_resolved_item(
                        &resolved_item,
                        trace.clone(),
                    );
                let mut value = Expr::Ident {
                    name,
                    variable_id,
                    type_args: new_type_args,
                };
                let mut ts = Vec::new();
                let mut fn_t = t.clone();
                for (_, _, implicit_arg_t, _) in
                    resolved_item.implicit_args.iter().rev()
                {
                    fn_t = TypeUnit::Fn(implicit_arg_t.clone(), fn_t)
                        .into();
                    ts.push(fn_t.clone());
                }
                for (
                    (_, name, implicit_arg_t, resolved_item),
                    fn_t,
                ) in resolved_item
                    .implicit_args
                    .iter()
                    .zip(ts.into_iter().rev())
                {
                    let (variable_id, type_args) = self
                        .get_variable_id_from_resolved_item(
                            &resolved_item
                                .clone()
                                .replace_variables(t_args),
                            trace.clone(),
                        );
                    value = Expr::Call(
                        Box::new((value, fn_t)),
                        Box::new((
                            Expr::Ident {
                                name,
                                variable_id,
                                type_args,
                            },
                            implicit_arg_t.clone(),
                        )),
                    );
                }
                value
            }
            ast_step3::Expr::Call(f, a) => Expr::Call(
                self.monomorphy_expr(*f, t_args, trace.clone())
                    .into(),
                self.monomorphy_expr(*a, t_args, trace).into(),
            ),
            ast_step3::Expr::Do(exprs) => Expr::DoBlock(
                exprs
                    .into_iter()
                    .map(|expr| {
                        self.monomorphy_expr(
                            expr,
                            t_args,
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

impl<'a> ResolvedIdent<'a> {
    fn replace_variables(
        mut self,
        type_args: &BTreeMap<TypeVariable, Type<'a>>,
    ) -> Self {
        self.type_args = type_args
            .iter()
            .map(|(v, t)| (*v, t.clone()))
            .chain(self.type_args.clone().into_iter())
            .map(|(v, mut t)| {
                for (from, to) in type_args {
                    t = t.replace_num(*from, to);
                }
                (v, t)
            })
            .collect();
        self.implicit_args = self
            .implicit_args
            .clone()
            .into_iter()
            .map(|(decl_id, name, mut t, v)| {
                for (from, to) in &self.type_args {
                    t = t.replace_num(*from, to);
                }
                (decl_id, name, t, v)
            })
            .collect();
        self
    }
}
