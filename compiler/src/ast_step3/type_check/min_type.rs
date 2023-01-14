use super::{
    Resolved, ResolvedIdent, TypeVariableMap, TypesOfLocalDeclsVec, VariableId,
};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::{self, Type, TypeUnit, TypeVariable};
use crate::ast_step2::{
    self, Expr, ExprWithTypeAndSpan, FnArm, Pattern, PatternRestriction,
    PatternRestrictions, PatternUnit, PatternUnitForRestriction, RelOrigin,
    SubtypeRelations,
};
use crate::errors::CompileError;
use fxhash::FxHashMap;
use itertools::Itertools;
use parser::Span;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VariableRequirement {
    pub name: parser::Path,
    pub module_path: Path,
    pub required_type: Type,
    pub ident: IdentId,
    pub span: Span,
    pub local_env: Vec<(String, DeclId, Type)>,
    pub req_recursion_count: usize,
}

pub fn min_type_with_env(
    e: &ExprWithTypeAndSpan<TypeVariable>,
    module_path: Path,
    map: &mut TypeVariableMap,
    imports: &mut Imports,
    token_map: &mut TokenMap,
    candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
) -> Result<
    (ast_step2::TypeWithEnv, Resolved, TypesOfLocalDeclsVec),
    CompileError,
> {
    let mut subtype_relations = Default::default();
    let mut pattern_restrictions = PatternRestrictions::default();
    let mut resolved = Default::default();
    let mut types_of_local_decls = Default::default();
    let mut req = Vec::new();
    let t = min_type_with_env_rec(
        e,
        module_path,
        &mut Env {
            subtype_relations: &mut subtype_relations,
            pattern_restrictions: &mut pattern_restrictions,
            resolved_idents: &mut resolved,
            types_of_decls: &mut types_of_local_decls,
            map,
            variable_requirements: &mut req,
        },
        &Default::default(),
    );
    let t = ast_step2::TypeWithEnv {
        constructor: t,
        variable_requirements: req
            .into_iter()
            .map(|r| {
                let name = imports.get_variables_with_path(
                    r.module_path,
                    if r.name.from_root {
                        Path::pkg_root()
                    } else {
                        r.module_path
                    },
                    &r.name.path,
                    token_map,
                    candidates_from_implicit_parameters,
                )?;
                Ok(super::VariableRequirement {
                    name,
                    module_path: r.module_path,
                    required_type: r.required_type,
                    ident: r.ident,
                    span: r.span,
                    local_env: r.local_env,
                    additional_candidates: candidates_from_implicit_parameters
                        .iter()
                        .map(|(a, b)| (a.to_string(), b.clone()))
                        .collect(),
                    req_recursion_count: r.req_recursion_count,
                })
            })
            .try_collect()?,
        subtype_relations,
        pattern_restrictions,
        fn_apply_dummies: Default::default(),
        already_considered_relations: Default::default(),
    };
    Ok((t, resolved, types_of_local_decls))
}

#[derive(Debug)]
struct Env<'a> {
    subtype_relations: &'a mut SubtypeRelations,
    pattern_restrictions: &'a mut PatternRestrictions,
    resolved_idents: &'a mut Resolved,
    types_of_decls: &'a mut TypesOfLocalDeclsVec,
    map: &'a mut TypeVariableMap,
    variable_requirements: &'a mut Vec<VariableRequirement>,
}

fn min_type_with_env_rec(
    (expr, type_variable, span): &ExprWithTypeAndSpan<TypeVariable>,
    module_path: Path,
    env: &mut Env<'_>,
    bindings: &FxHashMap<String, (DeclId, types::Type)>,
) -> Type {
    match expr {
        Expr::Lambda(arms) => {
            let mut arm_types = Vec::new();
            let mut restrictions = Vec::new();
            for arm in arms {
                let t = arm_min_type(arm, module_path, env, bindings);
                arm_types.push(t.arm_types);
                restrictions.push(t.restrictions);
            }
            let arg_len = arm_types.iter().map(Vec::len).min().unwrap() - 1;
            let mut arm_types =
                arm_types.into_iter().map(Vec::into_iter).collect_vec();
            let arg_types: Vec<Type> = (0..arg_len)
                .map(|_| {
                    let _t: Type = arm_types
                        .iter_mut()
                        .flat_map(|arm_type| arm_type.next().unwrap())
                        .collect();
                    TypeUnit::new_variable().into()
                })
                .collect();
            let rtn_type: Type =
                arm_types.into_iter().flat_map(types_to_fn_type).collect();
            let constructor: Type = types_to_fn_type(
                arg_types
                    .clone()
                    .into_iter()
                    .chain(std::iter::once(rtn_type)),
            );
            let restrictions = restrictions
                .into_iter()
                .map(|r| {
                    let (r, span) =
                PatternUnitForRestriction::argument_tuple_from_arguments(r);
                    (r, span.unwrap())
                })
                .collect();
            env.pattern_restrictions.push(PatternRestriction {
                type_: Type::argument_tuple_from_arguments(arg_types),
                pattern: restrictions,
                span: span.clone(),
                allow_inexhaustive: false,
            });
            env.map.insert(
                env.subtype_relations,
                *type_variable,
                constructor.clone(),
            );
            constructor
        }
        Expr::Number(_) => {
            let t = Type::intrinsic_from_str("I64");
            env.map
                .insert(env.subtype_relations, *type_variable, t.clone());
            t
        }
        Expr::StrLiteral(_) => {
            let t = Type::intrinsic_from_str("String");
            env.map
                .insert(env.subtype_relations, *type_variable, t.clone());
            t
        }
        Expr::Ident { name, ident_id } => {
            let t: Type = TypeUnit::Variable(*type_variable).into();
            register_requirement(
                VariableRequirement {
                    name: (*name).clone(),
                    module_path,
                    required_type: t.clone(),
                    ident: *ident_id,
                    local_env: Default::default(),
                    span: span.clone(),
                    req_recursion_count: 0,
                },
                bindings,
                env,
            );
            t
        }
        Expr::ResolvedIdent { type_, .. } => {
            env.map.insert(
                env.subtype_relations,
                *type_variable,
                type_.clone(),
            );
            type_.clone()
        }
        Expr::Call(f, a) => {
            let f_t = min_type_with_env_rec(f, module_path, env, bindings);
            let a_t = min_type_with_env_rec(a, module_path, env, bindings);
            let b: types::Type = TypeUnit::Variable(*type_variable).into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn: Type = TypeUnit::Fn(c.clone(), b.clone()).into();
            env.map.insert_type(
                env.subtype_relations,
                f_t.clone(),
                cb_fn.clone(),
                Some(RelOrigin {
                    left: f_t,
                    right: cb_fn,
                    span: f.2.clone(),
                }),
            );
            env.subtype_relations.insert((
                a_t.clone(),
                c.clone(),
                RelOrigin {
                    left: a_t,
                    right: c,
                    span: a.2.clone(),
                },
            ));
            b
        }
        Expr::Do(es) => {
            let t = es
                .iter()
                .map(|e| min_type_with_env_rec(e, module_path, env, bindings))
                .collect::<Vec<_>>();
            let t = t.last().unwrap().clone();
            env.map
                .insert(env.subtype_relations, *type_variable, t.clone());
            t
        }
        Expr::TypeAnnotation(e, annotation) => {
            let t = min_type_with_env_rec(e, module_path, env, bindings);
            env.subtype_relations.insert((
                t.clone(),
                annotation.clone(),
                RelOrigin {
                    left: t,
                    right: annotation.clone(),
                    span: span.clone(),
                },
            ));
            annotation.clone()
        }
    }
}

fn types_to_fn_type(types: impl DoubleEndedIterator<Item = Type>) -> Type {
    let mut ts = types.rev();
    let mut r = ts.next().unwrap();
    for t in ts {
        r = TypeUnit::Fn(t, r).into()
    }
    r
}

struct ArmType {
    arm_types: Vec<types::Type>,
    restrictions: Vec<(PatternUnitForRestriction, Span)>,
}

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type(
    arm: &FnArm<TypeVariable>,
    module_path: Path,
    env: &mut Env<'_>,
    bindings: &FxHashMap<String, (DeclId, types::Type)>,
) -> ArmType {
    let mut bindings = bindings.clone();
    let (mut ts, restrictions): (Vec<_>, Vec<_>) = arm
        .pattern
        .iter()
        .map(|(p, span)| {
            let (t, rest) = pattern_to_type(
                p,
                span.clone(),
                module_path,
                env,
                &mut bindings,
            );
            (t, rest)
        })
        .multiunzip();
    let body_type =
        min_type_with_env_rec(&arm.expr, module_path, env, &bindings);
    ts.push(body_type);
    ArmType {
        arm_types: ts,
        restrictions,
    }
}

fn register_requirement(
    mut req: VariableRequirement,
    bindings: &FxHashMap<String, (DeclId, types::Type)>,
    env: &mut Env<'_>,
) {
    match bindings.get(&req.name.path[0].0) {
        Some(a) if req.name.path.len() == 1 && !req.name.from_root => {
            env.map.insert_type(
                env.subtype_relations,
                a.1.clone(),
                req.required_type.clone(),
                Some(RelOrigin {
                    left: a.1.clone(),
                    right: req.required_type.clone(),
                    span: req.span,
                }),
            );
            env.resolved_idents.push((
                req.ident,
                ResolvedIdent {
                    variable_id: VariableId::Local(a.0),
                    implicit_args: Vec::new(),
                },
            ));
        }
        _ => {
            req.local_env.extend(bindings.iter().map(
                |(name, (decl_id, t))| (name.clone(), *decl_id, t.clone()),
            ));
            env.variable_requirements.push(req);
        }
    }
}

fn pattern_unit_to_type(
    p: &PatternUnit<TypeVariable>,
    bindings: &mut FxHashMap<String, (DeclId, types::Type)>,
    span: Span,
    module_path: Path,
    env: &mut Env<'_>,
) -> (types::Type, PatternUnitForRestriction) {
    use PatternUnit::*;
    match p {
        I64(_) => (
            Type::intrinsic_from_str("I64"),
            PatternUnitForRestriction::I64,
        ),
        Str(_) => (
            Type::intrinsic_from_str("String"),
            PatternUnitForRestriction::Str,
        ),
        Constructor { id, args, .. } => {
            let (types, pattern_restrictions): (Vec<_>, Vec<_>) = args
                .iter()
                .map(|p| {
                    let (t, res) = pattern_to_type(
                        p,
                        span.clone(),
                        module_path,
                        env,
                        bindings,
                    );
                    (t, res)
                })
                .multiunzip();
            (
                TypeUnit::Tuple(
                    TypeUnit::Const { id: (*id).into() }.into(),
                    Type::argument_tuple_from_arguments(types),
                )
                .into(),
                PatternUnitForRestriction::Tuple(
                    PatternUnitForRestriction::Const { id: (*id).into() }
                        .into(),
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        pattern_restrictions,
                    )
                    .0
                    .into(),
                ),
            )
        }
        Binder(name, decl_id, t) => {
            let t = Type::from(TypeUnit::Variable(*t));
            bindings.insert(name.to_string(), (*decl_id, t.clone()));
            env.types_of_decls
                .push((VariableId::Local(*decl_id), t.clone()));
            (t.clone(), PatternUnitForRestriction::Binder(t, *decl_id))
        }
        ResolvedBinder(decl_id, t) => (
            TypeUnit::Variable(*t).into(),
            PatternUnitForRestriction::Binder(
                TypeUnit::Variable(*t).into(),
                *decl_id,
            ),
        ),
        Underscore => {
            let v = TypeVariable::new();
            (
                TypeUnit::Variable(v).into(),
                PatternUnitForRestriction::Binder(
                    TypeUnit::Variable(v).into(),
                    DeclId::new(),
                ),
            )
        }
        TypeRestriction(p, t) => {
            let (_, (pattern_restriction, _span)) =
                pattern_to_type(p, span, module_path, env, bindings);
            (
                t.clone(),
                PatternUnitForRestriction::TypeRestriction(
                    Box::new(pattern_restriction),
                    t.clone(),
                ),
            )
        }
        Apply(pre_pattern, applications) => {
            let (t, (pattern_restriction, _)) = pattern_to_type(
                pre_pattern,
                span.clone(),
                module_path,
                env,
                bindings,
            );
            let mut all_post_patterns_are_bind = true;
            for a in applications {
                let function_t = min_type_with_env_rec(
                    &a.function,
                    module_path,
                    env,
                    bindings,
                );
                let post_pattern_t = Type::from(TypeUnit::new_variable());
                let (_, r) = pattern_to_type(
                    &a.post_pattern,
                    span.clone(),
                    module_path,
                    env,
                    bindings,
                );
                if !matches!(r.0, PatternUnitForRestriction::Binder(_, _)) {
                    all_post_patterns_are_bind = false;
                }
                let (r, span) =
                    PatternUnitForRestriction::argument_tuple_from_arguments(
                        vec![r],
                    );
                env.pattern_restrictions.push(PatternRestriction {
                    type_: Type::argument_tuple_from_arguments(vec![
                        post_pattern_t.clone(),
                    ]),
                    pattern: vec![(r, span.clone().unwrap())],
                    span: span.unwrap(),
                    allow_inexhaustive: true,
                });
                let function_t_expected =
                    Type::from(TypeUnit::Fn(t.clone(), post_pattern_t));
                env.subtype_relations.insert((
                    function_t.clone(),
                    function_t_expected.clone(),
                    RelOrigin {
                        left: function_t,
                        right: function_t_expected,
                        span: a.function.2.clone(),
                    },
                ));
            }
            (
                t,
                if all_post_patterns_are_bind {
                    pattern_restriction
                } else {
                    PatternUnitForRestriction::Apply(Box::new(
                        pattern_restriction,
                    ))
                },
            )
        }
    }
}

fn pattern_to_type(
    p: &Pattern<TypeVariable>,
    span: Span,
    module_path: Path,
    env: &mut Env<'_>,
    bindings: &mut FxHashMap<String, (DeclId, types::Type)>,
) -> (Type, (PatternUnitForRestriction, Span)) {
    if p.0.len() >= 2 {
        unimplemented!()
    }
    let mut ps = p.0.iter();
    let first_p = ps.next().unwrap();
    let (t, pattern) =
        pattern_unit_to_type(first_p, bindings, span.clone(), module_path, env);
    (t, (pattern, span))
}
