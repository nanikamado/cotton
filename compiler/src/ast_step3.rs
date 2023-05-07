mod type_check;
pub mod type_util;

pub use self::type_check::{
    simplify_subtype_rel, GlobalVariableType, LocalVariableType, ResolvedIdent,
    TypeVariableMap, VariableId, VariableIdInScope, VariableRequirement,
};
use self::type_check::{type_check, TypeCheckResult};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::{TypeConstructor, TypeUnit, TypeVariable};
use crate::ast_step2::{self, ApplyPattern, ConstructorId, PatternUnit};
use crate::errors::CompileError;
use doki::intrinsics::{IntrinsicConstructor, IntrinsicVariable};
use fxhash::FxHashMap;
use itertools::Itertools;
use strum::IntoEnumIterator;

/// Difference between `ast_step2::Ast` and `ast_step3::Ast`:
/// - The names of variables are resolved.
/// - Implicit parameters are converted to explicit parameters.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decls: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: Option<DeclId>,
    pub types_of_global_decls: FxHashMap<VariableId, GlobalVariableType>,
    pub types_of_local_decls: FxHashMap<VariableId, LocalVariableType>,
    pub basic_call_decls: FxHashMap<VariableId, DeclId>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: Path,
    pub value: Expr<'a>,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: String,
        variable_id: VariableId,
    },
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    DoBlock(Vec<Expr<'a>>),
    IntrinsicCall {
        args: Vec<Expr<'a>>,
        id: BasicFunction,
    },
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum BasicFunction {
    Intrinsic(IntrinsicVariable),
    Construction(ConstructorId),
    FieldAccessor { constructor: DeclId, field: usize },
}

pub type Pattern<'a> = ast_step2::Pattern<'a, (), Expr<'a>>;

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: Expr<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Path,
    pub field_len: usize,
    pub decl_id: DeclId,
}

impl<'a> Ast<'a> {
    pub fn from(
        ast: ast_step2::Ast<'a>,
        token_map: &mut TokenMap,
        imports: &mut Imports,
    ) -> Result<(Self, FxHashMap<IdentId, ResolvedIdent>), CompileError> {
        let TypeCheckResult {
            resolved_idents,
            global_variable_types,
            local_variable_types,
        } = type_check(&ast, token_map, imports)?;
        let mut variable_decls: Vec<VariableDecl> = Vec::new();
        let mut basic_call_decls: FxHashMap<VariableId, DeclId> =
            FxHashMap::default();
        for v in IntrinsicVariable::iter() {
            let d = basic_call(
                Path::from_str_intrinsic(v.to_str()),
                v.parameter_len(),
                BasicFunction::Intrinsic(v),
            );
            basic_call_decls
                .insert(VariableId::IntrinsicVariable(v), d.decl_id);
            variable_decls.push(d);
        }
        for v in IntrinsicConstructor::iter() {
            let d = basic_call(
                Path::from_str_intrinsic(v.to_str()),
                0,
                BasicFunction::Construction(ConstructorId::Intrinsic(v)),
            );
            basic_call_decls
                .insert(VariableId::IntrinsicConstructor(v), d.decl_id);
            variable_decls.push(d);
        }
        for v in &ast.data_decl {
            let d = basic_call(
                v.name,
                v.fields.len(),
                BasicFunction::Construction(ConstructorId::DeclId(v.decl_id)),
            );
            basic_call_decls
                .insert(VariableId::Constructor(v.decl_id), d.decl_id);
            variable_decls.push(d);
            for i in 0..v.fields.len() {
                let d = basic_call(
                    Path::from_str(Path::root(), "field_accessor"),
                    1,
                    BasicFunction::FieldAccessor {
                        constructor: v.decl_id,
                        field: i,
                    },
                );
                let decl_id = d.decl_id;
                basic_call_decls.insert(
                    VariableId::FieldAccessor {
                        constructor: v.decl_id,
                        field: i,
                    },
                    decl_id,
                );
                variable_decls.push(d);
            }
        }
        let resolved_idents = resolved_idents
            .into_iter()
            .map(|(ident_id, r)| match &r.variable_id {
                VariableId::IntrinsicVariable(_)
                | VariableId::Constructor(_)
                | VariableId::IntrinsicConstructor(_)
                | VariableId::FieldAccessor { .. } => {
                    debug_assert!(r.implicit_args.is_empty());
                    (
                        ident_id,
                        ResolvedIdent {
                            variable_id: VariableId::Global(
                                basic_call_decls[&r.variable_id],
                            ),
                            implicit_args: Vec::new(),
                        },
                    )
                }
                _ => (ident_id, r),
            })
            .collect();
        let mut env = Env {
            resolved_idents: &resolved_idents,
            types_of_decls: local_variable_types,
            basic_call_decls,
            additional_variable_decls: variable_decls,
        };
        let mut variable_decls = variable_decl(ast.variable_decl, &mut env);
        for v in &variable_decls {
            log::debug!(
                "type_ {} : {}",
                v.name,
                global_variable_types[&VariableId::Global(v.decl_id)].t
            );
        }
        variable_decls.append(&mut env.additional_variable_decls);
        let data_decl: Vec<DataDecl> = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
                field_len: d.fields.len(),
                decl_id: d.decl_id,
            })
            .collect();
        Ok((
            Self {
                variable_decls,
                data_decl,
                entry_point: ast.entry_point,
                types_of_global_decls: global_variable_types,
                types_of_local_decls: env.types_of_decls,
                basic_call_decls: env.basic_call_decls,
            },
            resolved_idents,
        ))
    }
}

fn basic_call(
    name: Path,
    param_len: usize,
    basic_function: BasicFunction,
) -> VariableDecl<'static> {
    let params = (0..param_len).map(|_| DeclId::new()).collect_vec();
    let mut v = Expr::IntrinsicCall {
        args: params
            .iter()
            .map(|decl_id| Expr::Ident {
                variable_id: VariableId::Local(*decl_id),
                name: "unnamed".to_string(),
            })
            .collect(),
        id: basic_function,
    };
    for decl_id in params.iter().rev() {
        v = Expr::Lambda(vec![FnArm {
            pattern: vec![ast_step2::Pattern(vec![PatternUnit::Binder(
                "unnamed".to_string(),
                *decl_id,
                (),
            )])],
            expr: v,
        }]);
    }
    let decl_id = DeclId::new();
    VariableDecl {
        name,
        value: v,
        decl_id,
    }
}

struct Env<'a, 'b> {
    resolved_idents: &'a FxHashMap<IdentId, ResolvedIdent>,
    types_of_decls: FxHashMap<VariableId, LocalVariableType>,
    basic_call_decls: FxHashMap<VariableId, DeclId>,
    additional_variable_decls: Vec<VariableDecl<'b>>,
}

fn variable_decl<'a>(
    variable_decls: Vec<ast_step2::VariableDecl<'a>>,
    env: &mut Env,
) -> Vec<VariableDecl<'a>> {
    variable_decls
        .into_iter()
        .map(|d| {
            let mut value = expr(d.value, env);
            for (name, t, decl_id) in d
                .type_annotation
                .into_iter()
                .flat_map(|ann| ann.implicit_parameters)
                .rev()
            {
                env.types_of_decls.insert(
                    VariableId::Local(decl_id),
                    LocalVariableType {
                        t: t.clone(),
                        toplevel: d.decl_id,
                    },
                );
                value = Expr::Lambda(vec![FnArm {
                    pattern: vec![ast_step2::Pattern(vec![
                        PatternUnit::Binder(name, decl_id, ()),
                    ])],
                    expr: value,
                }]);
            }
            VariableDecl {
                name: d.name,
                value,
                decl_id: d.decl_id,
            }
        })
        .collect()
}

fn expr<'a>(
    (e, _, _): ast_step2::ExprWithTypeAndSpan<'a, TypeVariable>,
    env: &mut Env,
) -> Expr<'a> {
    let e = match e {
        ast_step2::Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter()
                .map(|a| {
                    let e = expr(a.expr, env);
                    FnArm {
                        pattern: a
                            .pattern
                            .into_iter()
                            .map(|(p, _span)| {
                                normalize_types_in_pattern(p, env)
                            })
                            .collect(),
                        expr: e,
                    }
                })
                .collect(),
        ),
        ast_step2::Expr::Number(a) => Expr::Number(a),
        ast_step2::Expr::StrLiteral(a) => Expr::StrLiteral(a),
        ast_step2::Expr::Ident { name, ident_id } => {
            let resolved_item = env.resolved_idents[&ident_id].clone();
            get_expr_from_resolved_ident(
                name.path.last().unwrap().0.to_string(),
                &resolved_item,
                env.resolved_idents,
            )
        }
        ast_step2::Expr::ResolvedIdent {
            variable_id: variable_id @ VariableId::Local(_),
            ..
        } => Expr::Ident {
            name: "unique".to_string(),
            variable_id,
        },
        ast_step2::Expr::ResolvedIdent {
            variable_id, name, ..
        } => Expr::Ident {
            name: name.unwrap().to_string(),
            variable_id: match variable_id {
                VariableId::IntrinsicVariable(_)
                | VariableId::Constructor(_)
                | VariableId::IntrinsicConstructor(_)
                | VariableId::FieldAccessor { .. } => {
                    VariableId::Global(env.basic_call_decls[&variable_id])
                }
                _ => variable_id,
            },
        },
        ast_step2::Expr::Call(f, a) => {
            Expr::Call(expr(*f, env).into(), expr(*a, env).into())
        }
        ast_step2::Expr::Do(es) => {
            Expr::DoBlock(es.into_iter().map(|e| expr(e, env)).collect())
        }
        ast_step2::Expr::TypeAnnotation(v, _) => return expr(*v, env),
    };
    e
}

fn get_expr_from_resolved_ident(
    name: String,
    resolved_ident: &ResolvedIdent,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
) -> Expr<'static> {
    let mut value = Expr::Ident {
        name,
        variable_id: resolved_ident.variable_id,
    };
    for (name, _, resolved_ident) in &resolved_ident.implicit_args {
        value = Expr::Call(
            Box::new(value),
            Box::new(get_expr_from_resolved_ident(
                name.to_string(),
                &resolved_idents[resolved_ident],
                resolved_idents,
            )),
        );
    }
    value
}

#[allow(unused)]
/// Change `Cons[List[a], a] | Nil` to `List[a]`
fn lift_recursive_alias<T>(t: T) -> T
where
    T: TypeConstructor,
{
    if let Some(body) = t.find_recursive_alias().cloned() {
        let r = &TypeUnit::RecursiveAlias { body: body.clone() };
        let v = TypeVariable::new();
        let t = t.replace_type(r, &TypeUnit::Variable(v));
        let body = body.replace_num(
            TypeVariable::RecursiveIndex(0),
            &TypeUnit::Variable(v).into(),
        );
        let (t, updated) = t.replace_type_union_with_update_flag(
            &body,
            &TypeUnit::Variable(v),
            0,
        );
        let t = t.replace_num(v, &r.clone().into());
        if updated {
            lift_recursive_alias(t)
        } else {
            t
        }
    } else {
        t
    }
}

fn normalize_types_in_pattern<'a>(
    pattern: ast_step2::Pattern<'a, TypeVariable>,
    env: &mut Env<'_, '_>,
) -> Pattern<'a> {
    ast_step2::Pattern(
        pattern
            .0
            .into_iter()
            .map(|p| normalize_types_in_pattern_unit(p, env))
            .collect(),
    )
}

fn normalize_types_in_pattern_unit<'a>(
    pattern: PatternUnit<'a, TypeVariable>,
    env: &mut Env,
) -> PatternUnit<'a, (), Expr<'a>> {
    match pattern {
        PatternUnit::Binder(name, ident_id, _) => {
            PatternUnit::Binder(name, ident_id, ())
        }
        PatternUnit::ResolvedBinder(decl_id, _) => {
            PatternUnit::Binder("unique".to_string(), decl_id, ())
        }
        PatternUnit::I64(a) => PatternUnit::I64(a),
        PatternUnit::Str(a) => PatternUnit::Str(a),
        PatternUnit::Constructor { id, args } => PatternUnit::Constructor {
            id,
            args: args
                .into_iter()
                .map(|(p, span)| (normalize_types_in_pattern(p, env), span))
                .collect(),
        },
        PatternUnit::Underscore => PatternUnit::Underscore,
        PatternUnit::TypeRestriction(p, t) => {
            PatternUnit::TypeRestriction(normalize_types_in_pattern(p, env), t)
        }
        PatternUnit::Apply(pre_pattern, applications) => PatternUnit::Apply(
            Box::new(normalize_types_in_pattern(*pre_pattern, env)),
            applications
                .into_iter()
                .map(|a| ApplyPattern {
                    function: expr(a.function, env),
                    post_pattern: normalize_types_in_pattern(
                        a.post_pattern,
                        env,
                    ),
                })
                .collect(),
        ),
    }
}
