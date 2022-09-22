use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        types::{Type, TypeVariable},
        Pattern, PatternUnit,
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
    pub value: Expr<'a>,
    pub decl_id: DeclId,
}

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
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    DoBlock(Vec<Expr<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: Expr<'a>,
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
    map:
        FxHashMap<(DeclId, BTreeMap<TypeVariable, Type<'a>>), VariableDecl<'a>>,
    variable_decls: FxHashMap<DeclId, &'b ast_step3::VariableDecl<'a>>,
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
    let data_decls: FxHashMap<DeclId, &ast_step2::DataDecl<'a>> = data_decls
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
    let decls = monomorphics.map.into_iter().map(|(_, d)| d).collect();
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
        } else if let Some(d) = self.map.get(&(old_decl_id, type_args.clone()))
        {
            d.decl_id
        } else if let Some(d) = self.variable_decls.get(&old_decl_id) {
            let d = (*d).clone();
            let new_decl_id = DeclId::new();
            trace.insert(old_decl_id, new_decl_id);
            let mut value = self.monomorphy_expr(d.value, trace);
            for (decl_id, name, t) in implicit_args.into_iter().rev() {
                value = Expr::Lambda(vec![FnArm {
                    pattern: vec![vec![PatternUnit::Binder(
                        name,
                        decl_id,
                        t.clone(),
                    )]],
                    expr: value,
                }]);
            }
            let value = value;
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
                        d.fields.iter().map(|v| type_args[v].clone()).collect(),
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
                                .map(|(i, name, t, _)| (*i, *name, t.clone()))
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
        e: ast_step3::Expr<'a>,
        trace: FxHashMap<DeclId, DeclId>,
    ) -> Expr<'a> {
        let e = match e {
            ast_step3::Expr::Lambda(arms) => Expr::Lambda(
                arms.into_iter()
                    .map(|a| {
                        let expr = self.monomorphy_expr(a.expr, trace.clone());
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
                let resolved_item =
                    self.resolved_idents.get(&ident_id).unwrap().clone();
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
                for (_, name, _implicit_arg_t, resolved_item) in
                    resolved_item.implicit_args.iter()
                {
                    let (variable_id, type_args) = self
                        .get_variable_id_from_resolved_item(
                            resolved_item,
                            trace.clone(),
                        );
                    value = Expr::Call(
                        Box::new(value),
                        Box::new(Expr::Ident {
                            name,
                            variable_id,
                            type_args,
                        }),
                    );
                }
                value
            }
            ast_step3::Expr::Call(f, a) => Expr::Call(
                self.monomorphy_expr(*f, trace.clone()).into(),
                self.monomorphy_expr(*a, trace).into(),
            ),
            ast_step3::Expr::Do(exprs) => Expr::DoBlock(
                exprs
                    .into_iter()
                    .map(|expr| self.monomorphy_expr(expr, trace.clone()))
                    .collect(),
            ),
        };
        e
    }
}
