use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::name_id::Path;
use crate::ast_step2::{types, ConstructorId, TypeId};
use crate::ast_step3::{BasicFunction, DataDecl, VariableId};
use crate::ast_step4::{self, PaddedTypeMap, Type, TypePointer};
use crate::intrinsics::IntrinsicVariable;
use fxhash::FxHashMap;
use itertools::Itertools;
use std::fmt::Display;

#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: LambdaId,
    pub functions: Vec<Function>,
    pub variable_names: FxHashMap<VariableId, String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: Path,
    pub value: ExprWithType,
    pub decl_id: DeclId,
}

pub type ExprWithType = (Expr, Type);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        tag: u32,
        lambda_id: LambdaId,
        context: Vec<DeclId>,
    },
    Match {
        arms: Vec<FnArm>,
        arguments: Vec<DeclId>,
    },
    Number(String),
    StrLiteral(String),
    Ident {
        variable_id: VariableId,
    },
    Call {
        possible_functions: Vec<LambdaId>,
        f: Box<ExprWithType>,
        a: Box<ExprWithType>,
    },
    DoBlock(Vec<ExprWithType>),
    BasicCall {
        args: Vec<ExprWithType>,
        id: BasicFunction,
    },
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Pattern {
    pub patterns: Vec<PatternUnit>,
    pub type_: Type,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit {
    I64(String),
    Str(String),
    Constructor {
        id: ConstructorId,
    },
    Binder(DeclId),
    Underscore,
    TypeRestriction(Pattern, types::Type),
    Apply {
        pre_pattern: Pattern,
        function: ExprWithType,
        possible_functions: Vec<LambdaId>,
        post_pattern: Pattern,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern>,
    pub expr: ExprWithType,
}

impl Ast {
    pub fn from(ast: ast_step4::Ast) -> Self {
        let mut memo = VariableMemo::new(ast.variable_decl, ast.type_map);
        memo.monomorphize_decl_rec(
            ast.entry_point,
            ast.type_of_entry_point,
            &Default::default(),
            &Default::default(),
        );
        let mut variable_names = ast.variable_names;
        for v in &memo.monomorphized_variables {
            variable_names
                .insert(VariableId::Global(v.decl_id), v.name.to_string());
        }
        if let Expr::Lambda { lambda_id, .. } =
            memo.monomorphized_variables.last().unwrap().value.0
        {
            Self {
                variable_decl: memo.monomorphized_variables,
                data_decl: ast.data_decl,
                entry_point: lambda_id,
                functions: memo
                    .functions
                    .into_values()
                    .map(|f| f.function.unwrap())
                    .collect(),
                variable_names,
            }
        } else {
            panic!()
        }
    }
}

pub struct VariableMemo {
    variable_decls: FxHashMap<DeclId, ast_step4::VariableDecl<TypePointer>>,
    monomorphized_variable_map: FxHashMap<(DeclId, Type), DeclId>,
    monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
    functions: FxHashMap<(u32, Type), FunctionEntry>,
}

#[derive(Debug)]
struct FunctionEntry {
    id: u32,
    function: Option<Function>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub parameter: DeclId,
    pub parameter_type: Type,
    pub body: ExprWithType,
    pub id: u32,
    pub original_id: u32,
    pub origin_type: Type,
    pub context: Vec<DeclId>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum LambdaId {
    Normal(u32),
    IntrinsicVariable(IntrinsicVariable, u32),
    Constructor(ConstructorId, u32),
    FieldAccessor { constructor: TypeId, field: usize },
}

impl VariableMemo {
    pub fn new(
        variable_decls: Vec<ast_step4::VariableDecl<TypePointer>>,
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
            functions: FxHashMap::default(),
        }
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
                    value: self.expr(d.value.clone(), &t, replace_map, &trace),
                    decl_id: new_decl_id,
                };
                self.monomorphized_variable_map
                    .insert((decl_id, t), new_decl_id);
                self.monomorphized_variables.push(d);
                new_decl_id
            }
        }
    }

    fn expr(
        &mut self,
        (e, t): ast_step4::ExprWithType,
        global_variable_type: &Type,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> ExprWithType {
        debug_assert_ne!(global_variable_type.len(), 0);
        use Expr::*;
        let e = match e {
            ast_step4::Expr::Lambda {
                lambda_number,
                context,
                parameter,
                parameter_type,
                body,
            } => {
                let possible_functions =
                    self.get_possible_functions(t, replace_map);
                let parameter_type = self
                    .map
                    .get_type_with_replace_map(parameter_type, replace_map);
                let f = Function {
                    parameter,
                    parameter_type,
                    body: self.expr(
                        *body,
                        global_variable_type,
                        replace_map,
                        trace,
                    ),
                    id: 0,
                    context: context.clone(),
                    original_id: lambda_number,
                    origin_type: global_variable_type.clone(),
                };
                let e = self
                    .functions
                    .get_mut(&(lambda_number, global_variable_type.clone()))
                    .unwrap();
                debug_assert!(e.function.is_none());
                e.function = Some(Function { id: e.id, ..f });
                let lambda_id = LambdaId::Normal(e.id);
                Lambda {
                    tag: possible_functions.binary_search(&lambda_id).unwrap()
                        as u32,
                    context,
                    lambda_id,
                }
            }
            ast_step4::Expr::Match { arms, arguments } => Match {
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        self.monomorphize_fn_arm(
                            arm,
                            replace_map,
                            global_variable_type,
                            trace,
                        )
                    })
                    .collect(),
                arguments,
            },
            ast_step4::Expr::Ident {
                variable_id:
                    VariableId::Global(_)
                    | VariableId::IntrinsicVariable(_)
                    | VariableId::IntrinsicConstructor(_)
                    | VariableId::Constructor(_),
            } => panic!(),
            ast_step4::Expr::Ident {
                variable_id: VariableId::FieldAccessor { constructor, field },
            } => {
                let possible_functions =
                    self.get_possible_functions(t, replace_map);
                let lambda_id = LambdaId::FieldAccessor {
                    constructor: TypeId::DeclId(constructor),
                    field,
                };
                Expr::Lambda {
                    tag: possible_functions.binary_search(&lambda_id).unwrap()
                        as u32,
                    lambda_id,
                    context: Vec::new(),
                }
            }
            ast_step4::Expr::Ident {
                variable_id: variable_id @ VariableId::Local(_),
            } => Ident { variable_id },
            ast_step4::Expr::GlobalVariable {
                decl_id,
                replace_map: r,
            } => Ident {
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
            ast_step4::Expr::Call(f, a) => {
                let possible_functions: Vec<_> =
                    self.get_possible_functions(f.1, replace_map);
                Call {
                    f: Box::new(self.expr(
                        *f,
                        global_variable_type,
                        replace_map,
                        trace,
                    )),
                    a: Box::new(self.expr(
                        *a,
                        global_variable_type,
                        replace_map,
                        trace,
                    )),
                    possible_functions,
                }
            }
            ast_step4::Expr::DoBlock(es) => DoBlock(
                es.into_iter()
                    .map(|e| {
                        self.expr(e, global_variable_type, replace_map, trace)
                    })
                    .collect(),
            ),
            ast_step4::Expr::IntrinsicCall { args, id } => BasicCall {
                args: args
                    .into_iter()
                    .map(|a| {
                        self.expr(a, global_variable_type, replace_map, trace)
                    })
                    .collect(),
                id,
            },
            ast_step4::Expr::Number(a) => Number(a),
            ast_step4::Expr::StrLiteral(a) => StrLiteral(a),
        };
        let t = self.map.get_type_with_replace_map(t, replace_map);
        (e, t)
    }

    fn get_possible_functions(
        &mut self,
        p: TypePointer,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
    ) -> Vec<LambdaId> {
        let (_, _, fn_id) = self.map.get_fn(p);
        self.map
            .get_lambda_id(fn_id, replace_map)
            .clone()
            .into_iter()
            .map(|id| match id {
                ast_step4::LambdaId::Normal(la, t) => {
                    let t = self.map.get_type_with_replace_map(t, replace_map);
                    let len = self.functions.len() as u32;
                    let id = self
                        .functions
                        .entry((la, t))
                        .or_insert(FunctionEntry {
                            id: len,
                            function: None,
                        })
                        .id;
                    LambdaId::Normal(id)
                }
                ast_step4::LambdaId::IntrinsicVariable(a, b) => {
                    LambdaId::IntrinsicVariable(a, b)
                }
                ast_step4::LambdaId::Constructor(a, b) => {
                    LambdaId::Constructor(a, b)
                }
                ast_step4::LambdaId::FieldAccessor { constructor, field } => {
                    LambdaId::FieldAccessor { constructor, field }
                }
            })
            .sorted_unstable()
            .collect()
    }

    fn monomorphize_fn_arm(
        &mut self,
        arm: ast_step4::FnArm,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        global_variable_type: &Type,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> FnArm {
        FnArm {
            pattern: arm
                .pattern
                .into_iter()
                .map(|p| {
                    self.monomorphize_pattern(
                        p,
                        replace_map,
                        global_variable_type,
                        trace,
                    )
                })
                .collect(),
            expr: self.expr(arm.expr, global_variable_type, replace_map, trace),
        }
    }

    fn monomorphize_pattern(
        &mut self,
        pattern: ast_step4::Pattern,
        replace_map: &FxHashMap<TypePointer, TypePointer>,
        global_variable_type: &Type,
        trace: &FxHashMap<DeclId, DeclId>,
    ) -> Pattern {
        let patterns = pattern
            .patterns
            .into_iter()
            .map(|p| {
                use self::PatternUnit::*;
                use ast_step4::PatternUnit;
                match p {
                    PatternUnit::Constructor { id } => Constructor { id },
                    PatternUnit::I64(a) => I64(a),
                    PatternUnit::Str(a) => Str(a),
                    PatternUnit::Binder(id) => Binder(id),
                    PatternUnit::Underscore => Underscore,
                    PatternUnit::TypeRestriction(p, t) => TypeRestriction(
                        self.monomorphize_pattern(
                            p,
                            replace_map,
                            global_variable_type,
                            trace,
                        ),
                        t,
                    ),
                    PatternUnit::Apply {
                        pre_pattern,
                        function,
                        post_pattern,
                    } => {
                        let p = function.1;
                        Apply {
                            pre_pattern: self.monomorphize_pattern(
                                pre_pattern,
                                replace_map,
                                global_variable_type,
                                trace,
                            ),
                            function: self.expr(
                                function,
                                global_variable_type,
                                replace_map,
                                trace,
                            ),
                            post_pattern: self.monomorphize_pattern(
                                post_pattern,
                                replace_map,
                                global_variable_type,
                                trace,
                            ),
                            possible_functions: self
                                .get_possible_functions(p, replace_map),
                        }
                    }
                }
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

impl Display for LambdaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LambdaId::Normal(a) => {
                write!(f, "la{a}")
            }
            LambdaId::IntrinsicVariable(a, b) => {
                write!(f, "intrinsic_{}_{b}", a.to_str())
            }
            LambdaId::Constructor(a, b) => {
                write!(f, "constructor_{a}_{b}")
            }
            LambdaId::FieldAccessor {
                constructor: _,
                field,
            } => {
                write!(f, "$field_accessor({field})")
            }
        }
    }
}
