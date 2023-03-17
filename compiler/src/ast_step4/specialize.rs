use crate::ast_step1::decl_id::DeclId;
use crate::ast_step3::VariableId;
use crate::ast_step4::{
    Expr, ExprWithType, FnArm, PaddedTypeMap, Pattern, PatternUnit, Type,
    TypePointer, VariableDecl,
};
use fxhash::FxHashMap;

pub struct VariableMemo {
    variable_decls: FxHashMap<DeclId, VariableDecl<TypePointer>>,
    monomorphized_variable_map: FxHashMap<(DeclId, Type), DeclId>,
    pub monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
}

impl VariableMemo {
    pub fn new(
        variable_decls: Vec<VariableDecl<TypePointer>>,
        map: PaddedTypeMap,
    ) -> Self {
        VariableMemo {
            variable_decls: variable_decls
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            monomorphized_variable_map: Default::default(),
            monomorphized_variables: Default::default(),
            map,
        }
    }

    pub fn monomorphize_decl(&mut self, decl_id: DeclId) -> DeclId {
        let p = self.map.new_pointer();
        self.monomorphize_decl_rec(
            decl_id,
            p,
            &Default::default(),
            &Default::default(),
        )
    }

    fn monomorphize_decl_rec(
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
        (e, t): ExprWithType,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType<Type> {
        use Expr::*;
        let e = match e {
            Expr::Lambda {
                lambda_number,
                context,
                parameter,
                parameter_type,
                body,
            } => Expr::Lambda {
                lambda_number,
                context,
                parameter,
                parameter_type: self
                    .map
                    .get_type_with_replace_map(parameter_type, replace_map),
                body: Box::new(self.monomorphize_expr(
                    *body,
                    replace_map,
                    trace,
                )),
            },
            Expr::Match { arms, arguments } => Expr::Match {
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        self.monomorphize_fn_arm(arm, replace_map, trace)
                    })
                    .collect(),
                arguments,
            },
            Expr::Ident {
                name,
                variable_id: VariableId::Global(decl_id),
            } => Ident {
                name,
                variable_id: VariableId::Global(self.monomorphize_decl_rec(
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
                    self.monomorphize_decl_rec(
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
        arm: FnArm,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> FnArm<Type> {
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
        pattern: Pattern<TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> Pattern<Type> {
        let patterns = pattern
            .patterns
            .into_iter()
            .map(|p| match p {
                PatternUnit::Constructor { name, id } => {
                    PatternUnit::Constructor { name, id }
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
        Pattern {
            patterns,
            type_: self
                .map
                .get_type_with_replace_map(pattern.type_, replace_map),
        }
    }
}
