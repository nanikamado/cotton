use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Name;
use crate::ast_step3::{DataDecl, VariableId};
use crate::ast_step4::{self, PaddedTypeMap, PatternUnit, Type, TypePointer};
use fxhash::FxHashMap;

/// Difference between `ast_step4::Ast` and `ast_step5::Ast`:
/// - Some global variables are replicated and types are upcasted
/// so that the arguments and parameters become the same type.
#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Ident {
        name: String,
        variable_id: VariableId,
    },
    Call(Box<ExprWithType>, Box<ExprWithType>),
    DoBlock(Vec<ExprWithType>),
}

pub type ExprWithType = (Expr, Type);

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub name: Name,
    pub value: ExprWithType,
    pub decl_id: DeclId,
}

pub type Pattern = ast_step4::Pattern<Type, ExprWithType>;

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub expr: ExprWithType,
}

impl From<ast_step4::Ast> for Ast {
    fn from(ast: ast_step4::Ast) -> Self {
        let mut memo = VariableMemo {
            variable_decls: ast
                .variable_decl
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            monomorphized_variable_map: Default::default(),
            monomorphized_variables: Default::default(),
            map: ast.map,
        };
        let p = memo.map.new_pointer();
        let entry_point = memo.monomorphize_decl(
            ast.entry_point,
            p,
            &Default::default(),
            &Default::default(),
        );
        Self {
            variable_decl: memo.monomorphized_variables,
            data_decl: ast
                .data_decl
                .into_iter()
                .map(|d| DataDecl {
                    name: d.name,
                    field_len: d.field_len,
                    decl_id: d.decl_id,
                })
                .collect(),
            entry_point,
        }
    }
}

struct VariableMemo {
    variable_decls: FxHashMap<DeclId, ast_step4::VariableDecl<TypePointer>>,
    monomorphized_variable_map: FxHashMap<(DeclId, Type), DeclId>,
    monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
}

impl VariableMemo {
    fn monomorphize_decl(
        &mut self,
        decl_id: DeclId,
        p: TypePointer,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> DeclId {
        if let Some(d) = trace.get(&decl_id) {
            *d
        } else {
            let t = self.map.get_type_with_replace_map(p, replace_map);
            let decl_id_t = (decl_id, t);
            if let Some(d) = self.monomorphized_variable_map.get(&decl_id_t) {
                *d
            } else {
                let (_, t) = decl_id_t;
                let new_decl_id = DeclId::new();
                let d = &self.variable_decls[&decl_id];
                let mut trace = trace.clone();
                trace.insert(decl_id, new_decl_id);
                let d = VariableDecl {
                    name: d.name,
                    value: self.monomorphize_expr(
                        d.value.clone(),
                        replace_map,
                        &trace,
                    ),
                    decl_id: new_decl_id,
                };
                self.monomorphized_variable_map
                    .insert((decl_id, t), new_decl_id);
                self.monomorphized_variables.push(d);
                new_decl_id
            }
        }
    }

    fn monomorphize_expr(
        &mut self,
        (e, t): ast_step4::ExprWithType,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType {
        use self::Expr::*;
        use ast_step4::Expr;
        let e = match e {
            Expr::Lambda(arms) => Lambda(
                arms.into_iter()
                    .map(|arm| {
                        self.monomorphize_fn_arm(arm, replace_map, trace)
                    })
                    .collect(),
            ),
            Expr::Ident {
                name,
                variable_id: VariableId::Global(decl_id),
            } => Ident {
                name,
                variable_id: VariableId::Global(self.monomorphize_decl(
                    decl_id,
                    t,
                    replace_map,
                    trace,
                )),
            },
            Expr::GlobalVariable {
                name,
                decl_id,
                replace_map: r,
            } => Ident {
                name,
                variable_id: VariableId::Global(
                    self.monomorphize_decl(
                        decl_id,
                        t,
                        &r.iter()
                            .map(|(from, to)| {
                                (*from, *replace_map.get(to).unwrap_or(to))
                            })
                            .chain(
                                replace_map
                                    .iter()
                                    .map(|(from, to)| (*from, *to)),
                            )
                            .collect(),
                        trace,
                    ),
                ),
            },
            Expr::Call(a, b) => Call(
                Box::new(self.monomorphize_expr(*a, replace_map, trace)),
                Box::new(self.monomorphize_expr(*b, replace_map, trace)),
            ),
            Expr::DoBlock(es) => DoBlock(
                es.into_iter()
                    .map(|e| self.monomorphize_expr(e, replace_map, trace))
                    .collect(),
            ),
            Expr::Number(a) => Number(a),
            Expr::StrLiteral(a) => StrLiteral(a),
            Expr::Ident { name, variable_id } => Ident { name, variable_id },
        };
        let t = self.map.get_type_with_replace_map(t, replace_map);
        (e, t)
    }

    fn monomorphize_fn_arm(
        &mut self,
        arm: ast_step4::FnArm,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> FnArm {
        FnArm {
            pattern: arm
                .pattern
                .into_iter()
                .map(|p| self.monomorphize_pattern(p, replace_map, trace))
                .collect(),
            expr: self.monomorphize_expr(arm.expr, replace_map, trace),
        }
    }

    fn monomorphize_pattern(
        &mut self,
        (pattern, t): ast_step4::Pattern<TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> Pattern {
        let pattern = pattern
            .into_iter()
            .map(|p| match p {
                PatternUnit::Constructor { name, id, args } => {
                    let args = args
                        .into_iter()
                        .map(|p| {
                            self.monomorphize_pattern(p, replace_map, trace)
                        })
                        .collect();
                    PatternUnit::Constructor { name, id, args }
                }
                PatternUnit::I64(a) => PatternUnit::I64(a),
                PatternUnit::Str(a) => PatternUnit::Str(a),
                PatternUnit::Binder(name, id) => PatternUnit::Binder(name, id),
                PatternUnit::Underscore => PatternUnit::Underscore,
                PatternUnit::TypeRestriction(p, t) => {
                    PatternUnit::TypeRestriction(
                        self.monomorphize_pattern(p, replace_map, trace),
                        t,
                    )
                }
                PatternUnit::Apply {
                    pre_pattern,
                    function,
                    post_pattern,
                } => PatternUnit::Apply {
                    pre_pattern: self.monomorphize_pattern(
                        pre_pattern,
                        replace_map,
                        trace,
                    ),
                    function: self.monomorphize_expr(
                        function,
                        replace_map,
                        trace,
                    ),
                    post_pattern: self.monomorphize_pattern(
                        post_pattern,
                        replace_map,
                        trace,
                    ),
                },
            })
            .collect();
        (pattern, self.map.get_type_with_replace_map(t, replace_map))
    }
}
