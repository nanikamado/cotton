use crate::{
    ast_step2::decl_id::DeclId,
    ast_step3::DataDecl,
    ast_step3::VariableId,
    ast_step5::{
        self, PaddedTypeMap, Pattern, PatternUnit, Type, TypePointer,
        VariableKind,
    },
};
use fxhash::FxHashMap;

#[derive(Debug)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: &'a str,
        variable_id: VariableId,
        variable_kind: VariableKind,
    },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

pub type ExprWithType<'a> = (Expr<'a>, Type<'a>);

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a, Type<'a>>>,
    pub expr: ExprWithType<'a>,
}

impl<'a> From<ast_step5::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step5::Ast<'a>) -> Self {
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
            data_decl: ast.data_decl,
            entry_point,
        }
    }
}

struct VariableMemo<'a> {
    variable_decls: FxHashMap<DeclId, ast_step5::VariableDecl<'a, TypePointer>>,
    monomorphized_variable_map: FxHashMap<(DeclId, Type<'a>), DeclId>,
    monomorphized_variables: Vec<VariableDecl<'a>>,
    map: PaddedTypeMap<'a>,
}

impl<'a> VariableMemo<'a> {
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
                    .insert((decl_id, t.clone()), new_decl_id);
                self.monomorphized_variables.push(d);
                new_decl_id
            }
        }
    }

    fn monomorphize_expr(
        &mut self,
        (e, t): ast_step5::ExprWithType<'a, TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType<'a> {
        use self::Expr::*;
        use ast_step5::Expr;
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
        arm: ast_step5::FnArm<'a, TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> FnArm<'a> {
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
        (pattern, t): Pattern<'a, TypePointer>,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
    ) -> Pattern<'a> {
        let pattern = pattern
            .into_iter()
            .map(|p| match p {
                PatternUnit::Constructor { id, args } => {
                    let args = args
                        .into_iter()
                        .map(|p| self.monomorphize_pattern(p, replace_map))
                        .collect();
                    PatternUnit::Constructor { id, args }
                }
                PatternUnit::I64(a) => PatternUnit::I64(a),
                PatternUnit::Str(a) => PatternUnit::Str(a),
                PatternUnit::Binder(name, id) => PatternUnit::Binder(name, id),
                PatternUnit::Underscore => PatternUnit::Underscore,
            })
            .collect();
        (pattern, self.map.get_type_with_replace_map(t, replace_map))
    }
}
