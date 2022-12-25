use crate::{
    ast_step1::{decl_id::DeclId, name_id::Name},
    ast_step3::{DataDecl, VariableId, VariableKind},
    ast_step4::{self, PaddedTypeMap, Pattern, PatternUnit, Type, TypePointer},
};
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
        name: Name,
        variable_id: VariableId,
        variable_kind: VariableKind,
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

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern<Type>>,
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
        (e, t): ast_step4::ExprWithType<TypePointer>,
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
                variable_id: VariableId::Decl(decl_id),
                variable_kind: VariableKind::Global,
            } => Ident {
                name,
                variable_id: VariableId::Decl(self.monomorphize_decl(
                    decl_id,
                    t,
                    replace_map,
                    trace,
                )),
                variable_kind: VariableKind::Global,
            },
            Expr::GlobalVariable {
                name,
                decl_id,
                replace_map: r,
            } => Ident {
                name,
                variable_id: VariableId::Decl(
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
                variable_kind: VariableKind::Global,
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
            Expr::Ident {
                name,
                variable_id,
                variable_kind,
            } => Ident {
                name,
                variable_id,
                variable_kind,
            },
        };
        let t = self.map.get_type_with_replace_map(t, replace_map);
        (e, t)
    }

    fn monomorphize_fn_arm(
        &mut self,
        arm: ast_step4::FnArm<TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> FnArm {
        FnArm {
            pattern: arm
                .pattern
                .into_iter()
                .map(|p| self.monomorphize_pattern(p, replace_map))
                .collect(),
            expr: self.monomorphize_expr(arm.expr, replace_map, trace),
        }
    }

    fn monomorphize_pattern(
        &mut self,
        (pattern, t): Pattern<TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
    ) -> Pattern {
        let pattern = pattern
            .into_iter()
            .map(|p| match p {
                PatternUnit::Constructor { name, id, args } => {
                    let args = args
                        .into_iter()
                        .map(|p| self.monomorphize_pattern(p, replace_map))
                        .collect();
                    PatternUnit::Constructor { name, id, args }
                }
                PatternUnit::I64(a) => PatternUnit::I64(a),
                PatternUnit::Str(a) => PatternUnit::Str(a),
                PatternUnit::Binder(name, id) => PatternUnit::Binder(name, id),
                PatternUnit::Underscore => PatternUnit::Underscore,
                PatternUnit::TypeRestriction(p, t) => {
                    PatternUnit::TypeRestriction(
                        self.monomorphize_pattern(p, replace_map),
                        t,
                    )
                }
            })
            .collect();
        (pattern, self.map.get_type_with_replace_map(t, replace_map))
    }
}
