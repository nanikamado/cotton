use super::{
    Resolved, ResolvedIdent, TypeVariableMap, TypesOfLocalDeclsVec, VariableId,
};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::{self, Type, TypeUnit, TypeVariable};
use crate::ast_step2::{
    self, Expr, ExprWithTypeAndSpan, FnArm, Pattern, PatternRestrictions,
    PatternUnit, PatternUnitForRestriction, RelOrigin, SubtypeRelations,
};
use crate::ast_step3::VariableKind;
use crate::errors::CompileError;
use fxhash::FxHashMap;
use itertools::Itertools;
use parser::token_id::TokenId;
use parser::Span;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
struct TypeWithEnv {
    pub constructor: Type,
    pub variable_requirements: Vec<VariableRequirement>,
    pub subtype_relations: SubtypeRelations,
    pub already_considered_relations: BTreeSet<(Type, Type)>,
    pub pattern_restrictions: PatternRestrictions,
    pub fn_apply_dummies: BTreeMap<Type, (Type, RelOrigin)>,
}

impl From<Type> for TypeWithEnv {
    fn from(value: Type) -> Self {
        Self {
            constructor: value,
            ..Default::default()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VariableRequirement {
    pub name: Vec<(String, Option<Span>, Option<TokenId>)>,
    pub module_path: Name,
    pub required_type: Type,
    pub ident: IdentId,
    pub span: Span,
    pub local_env: Vec<(String, DeclId, Type)>,
    pub req_recursion_count: usize,
}

pub fn min_type_with_env(
    e: &ExprWithTypeAndSpan<TypeVariable>,
    module_path: Name,
    subtype_relations: &mut SubtypeRelations,
    map: &mut TypeVariableMap,
    imports: &mut Imports,
    token_map: &mut TokenMap,
    candidates_from_implicit_parameters: &FxHashMap<&str, Vec<DeclId>>,
) -> Result<
    (ast_step2::TypeWithEnv, Resolved, TypesOfLocalDeclsVec),
    CompileError,
> {
    let (t, resolved, types_of_local_decls) =
        min_type_with_env_rec(e, module_path, subtype_relations, map);
    let t = ast_step2::TypeWithEnv {
        constructor: t.constructor,
        variable_requirements: t
            .variable_requirements
            .into_iter()
            .map(|r| {
                let name = imports.get_variables_with_path(
                    r.module_path,
                    r.module_path,
                    &r.name
                        .iter()
                        .map(|(a, b, c)| (a.as_str(), b.clone(), *c))
                        .collect_vec(),
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
        subtype_relations: t.subtype_relations,
        already_considered_relations: t.already_considered_relations,
        pattern_restrictions: t.pattern_restrictions,
        fn_apply_dummies: t.fn_apply_dummies,
    };
    Ok((t, resolved, types_of_local_decls))
}

fn min_type_with_env_rec(
    (expr, type_variable, span): &ExprWithTypeAndSpan<TypeVariable>,
    module_path: Name,
    subtype_relations: &mut SubtypeRelations,
    map: &mut TypeVariableMap,
) -> (TypeWithEnv, Resolved, TypesOfLocalDeclsVec) {
    match expr {
        Expr::Lambda(arms) => {
            let mut arm_types = Vec::new();
            let mut restrictions = Vec::new();
            let mut variable_requirements = Vec::new();
            let mut subtype_relation = Vec::new();
            let mut resolved_idents = Vec::new();
            let mut pattern_restrictions = Vec::new();
            let mut types_of_decls = Vec::new();
            for arm in arms {
                let mut t =
                    arm_min_type(arm, module_path, subtype_relations, map);
                arm_types.push(t.arm_types);
                restrictions.push(t.restrictions);
                variable_requirements.append(&mut t.variable_requirements);
                subtype_relation.push(t.subtype_relation);
                resolved_idents.append(&mut t.resolved_idents);
                pattern_restrictions.append(&mut t.pattern_restrictions);
                types_of_decls.append(&mut t.types_of_decls);
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
            pattern_restrictions.push((
                Type::argument_tuple_from_arguments(arg_types),
                restrictions,
                span.clone(),
            ));
            map.insert(subtype_relations, *type_variable, constructor.clone());
            (
                TypeWithEnv {
                    constructor,
                    variable_requirements,
                    subtype_relations: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                    fn_apply_dummies: Default::default(),
                },
                resolved_idents,
                types_of_decls,
            )
        }
        Expr::Number(_) => {
            let t = Type::intrinsic_from_str("I64");
            map.insert(subtype_relations, *type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::StrLiteral(_) => {
            let t = Type::intrinsic_from_str("String");
            map.insert(subtype_relations, *type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::Ident { name, ident_id } => {
            let t: Type = TypeUnit::Variable(*type_variable).into();
            (
                TypeWithEnv {
                    constructor: t.clone(),
                    variable_requirements: vec![VariableRequirement {
                        name: name
                            .iter()
                            .map(|(a, b, c)| (a.to_string(), b.clone(), *c))
                            .collect(),
                        module_path,
                        required_type: t,
                        ident: *ident_id,
                        local_env: Default::default(),
                        span: span.clone(),
                        req_recursion_count: 0,
                    }],
                    subtype_relations: SubtypeRelations::default(),
                    pattern_restrictions: PatternRestrictions::default(),
                    already_considered_relations: Default::default(),
                    fn_apply_dummies: Default::default(),
                },
                Default::default(),
                Default::default(),
            )
        }
        Expr::ResolvedIdent { type_, .. } => {
            let t: Type = TypeUnit::Variable(*type_).into();
            map.insert(subtype_relations, *type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1, types_of_decls_f) =
                min_type_with_env_rec(f, module_path, subtype_relations, map);
            let (a_t, resolved2, types_of_decls_a) =
                min_type_with_env_rec(a, module_path, subtype_relations, map);
            let b: types::Type = TypeUnit::Variable(*type_variable).into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn: Type = TypeUnit::Fn(c.clone(), b.clone()).into();
            let mut f_eq_cb = Default::default();
            map.insert_type(
                &mut f_eq_cb,
                f_t.constructor.clone(),
                cb_fn.clone(),
                Some(RelOrigin {
                    left: f_t.constructor,
                    right: cb_fn,
                    span: f.2.clone(),
                }),
            );
            let a_sub_c = [(
                a_t.constructor.clone(),
                c.clone(),
                RelOrigin {
                    left: a_t.constructor,
                    right: c,
                    span: a.2.clone(),
                },
            )]
            .iter()
            .cloned()
            .collect();
            (
                TypeWithEnv {
                    constructor: b,
                    variable_requirements: [
                        f_t.variable_requirements,
                        a_t.variable_requirements,
                    ]
                    .concat(),
                    subtype_relations: vec![
                        f_eq_cb,
                        a_sub_c,
                        f_t.subtype_relations,
                        a_t.subtype_relations,
                    ]
                    .into_iter()
                    .flatten()
                    .collect(),
                    pattern_restrictions: [
                        f_t.pattern_restrictions,
                        a_t.pattern_restrictions,
                    ]
                    .concat(),
                    already_considered_relations: Default::default(),
                    fn_apply_dummies: Default::default(),
                },
                [resolved1, resolved2].concat(),
                [types_of_decls_f, types_of_decls_a].concat(),
            )
        }
        Expr::Do(es) => {
            let mut variable_requirements = Vec::new();
            let mut subtype_relations = SubtypeRelations::default();
            let mut resolved_idents = Vec::default();
            let mut pattern_restrictions = PatternRestrictions::default();
            let mut types_of_decls = Vec::new();
            let t = es
                .iter()
                .map(|e| {
                    let (t, resolved, mut tod) = min_type_with_env_rec(
                        e,
                        module_path,
                        &mut subtype_relations,
                        map,
                    );
                    variable_requirements
                        .append(&mut t.variable_requirements.clone());
                    subtype_relations.extend(t.subtype_relations.clone());
                    pattern_restrictions.extend(t.pattern_restrictions.clone());
                    resolved_idents.extend(resolved);
                    types_of_decls.append(&mut tod);
                    t
                })
                .collect::<Vec<_>>();
            let t = t.last().unwrap().clone();
            map.insert(
                &mut subtype_relations,
                *type_variable,
                t.constructor.clone(),
            );
            (
                TypeWithEnv {
                    constructor: t.constructor,
                    variable_requirements,
                    subtype_relations,
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                    fn_apply_dummies: Default::default(),
                },
                resolved_idents,
                types_of_decls,
            )
        }
        Expr::TypeAnnotation(e, annotation) => {
            let mut t =
                min_type_with_env_rec(e, module_path, subtype_relations, map);
            t.0.subtype_relations.insert((
                t.0.constructor.clone(),
                annotation.clone(),
                RelOrigin {
                    left: t.0.constructor.clone(),
                    right: annotation.clone(),
                    span: span.clone(),
                },
            ));
            t.0.constructor = annotation.clone();
            t
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
    variable_requirements: Vec<VariableRequirement>,
    subtype_relation: SubtypeRelations,
    resolved_idents: Resolved,
    pattern_restrictions: PatternRestrictions,
    types_of_decls: TypesOfLocalDeclsVec,
}

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type(
    arm: &FnArm<TypeVariable>,
    module_path: Name,
    subtype_relations: &mut SubtypeRelations,
    map: &mut TypeVariableMap,
) -> ArmType {
    let (body_type, mut resolved_idents, mut types_of_decls) =
        min_type_with_env_rec(&arm.expr, module_path, subtype_relations, map);
    let (mut ts, bindings, patterns): (Vec<_>, Vec<_>, Vec<_>) = arm
        .pattern
        .iter()
        .map(|(p, span)| pattern_to_type(p, span.clone()))
        .multiunzip();
    ts.push(body_type.constructor);
    let bindings: FxHashMap<String, (DeclId, types::Type)> = bindings
        .into_iter()
        .flatten()
        .inspect(|(_, (decl_id, t))| {
            types_of_decls.push((VariableId::Decl(*decl_id), t.clone()));
        })
        .collect();
    let mut variable_requirements = Vec::new();
    let mut subtype_requirement = Default::default();
    for mut p in body_type.variable_requirements.into_iter() {
        match bindings.get(&p.name[0].0) {
            Some(a) if p.name.len() == 1 => {
                map.insert_type(
                    &mut subtype_requirement,
                    a.1.clone(),
                    p.required_type.clone(),
                    Some(RelOrigin {
                        left: a.1.clone(),
                        right: p.required_type.clone(),
                        span: p.span,
                    }),
                );
                resolved_idents.push((
                    p.ident,
                    ResolvedIdent {
                        variable_id: VariableId::Decl(a.0),
                        implicit_args: Vec::new(),
                        variable_kind: VariableKind::Local,
                    },
                ));
            }
            _ => {
                p.local_env.extend(bindings.iter().map(
                    |(name, (decl_id, t))| (name.clone(), *decl_id, t.clone()),
                ));
                variable_requirements.push(p);
            }
        }
    }
    ArmType {
        arm_types: ts,
        restrictions: patterns,
        variable_requirements,
        subtype_relation: {
            let mut tmp = body_type.subtype_relations;
            tmp.extend(&mut subtype_requirement.into_iter());
            tmp
        },
        resolved_idents,
        pattern_restrictions: body_type.pattern_restrictions,
        types_of_decls,
    }
}

fn pattern_unit_to_type(
    p: &PatternUnit<TypeVariable>,
    span: Span,
) -> (
    types::Type,
    FxHashMap<String, (DeclId, types::Type)>,
    PatternUnitForRestriction,
) {
    use PatternUnit::*;
    match p {
        I64(_) => (
            Type::intrinsic_from_str("I64"),
            Default::default(),
            PatternUnitForRestriction::I64,
        ),
        Str(_) => (
            Type::intrinsic_from_str("String"),
            Default::default(),
            PatternUnitForRestriction::Str,
        ),
        Constructor { id, args, .. } => {
            let (types, bindings, pattern_restrictions): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = args
                .iter()
                .map(|p| pattern_to_type(p, span.clone()))
                .multiunzip();
            (
                TypeUnit::Tuple(
                    TypeUnit::Const { id: (*id).into() }.into(),
                    Type::argument_tuple_from_arguments(types),
                )
                .into(),
                // TypeUnit::new_variable().into(),
                bindings.into_iter().flatten().collect(),
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
        Binder(name, decl_id, t) => (
            TypeUnit::Variable(*t).into(),
            vec![(name.to_string(), (*decl_id, TypeUnit::Variable(*t).into()))]
                .into_iter()
                .collect(),
            PatternUnitForRestriction::Binder(
                TypeUnit::Variable(*t).into(),
                *decl_id,
            ),
        ),
        ResolvedBinder(decl_id, t) => (
            TypeUnit::Variable(*t).into(),
            Default::default(),
            PatternUnitForRestriction::Binder(
                TypeUnit::Variable(*t).into(),
                *decl_id,
            ),
        ),
        Underscore => {
            let v = TypeVariable::new();
            (
                TypeUnit::Variable(v).into(),
                Default::default(),
                PatternUnitForRestriction::Binder(
                    TypeUnit::Variable(v).into(),
                    DeclId::new(),
                ),
            )
        }
        TypeRestriction(p, t) => {
            let (_, binds, (pattern_restriction, _span)) =
                pattern_to_type(p, span);
            (
                t.clone(),
                binds,
                PatternUnitForRestriction::TypeRestriction(
                    Box::new(pattern_restriction),
                    t.clone(),
                ),
            )
        }
    }
}

#[allow(clippy::type_complexity)]
fn pattern_to_type(
    p: &Pattern<TypeVariable>,
    span: Span,
) -> (
    Type,
    FxHashMap<String, (DeclId, Type)>,
    (PatternUnitForRestriction, Span),
) {
    if p.len() >= 2 {
        unimplemented!()
    }
    let mut ps = p.iter();
    let first_p = ps.next().unwrap();
    let (mut t, mut binds, pattern) =
        pattern_unit_to_type(first_p, span.clone());
    for p in ps {
        let (t_, binds_, _pattern_) = pattern_unit_to_type(p, span.clone());
        t = t.union(t_);
        if binds.len() != binds_.len() {
            panic!("illegal pattern");
        }
        for ((name1, (id1, t1)), (name2, (id2, t2))) in
            binds.iter_mut().zip(binds_)
        {
            if *name1 != name2 || *id1 != id2 {
                panic!("illegal pattern");
            }
            *t1 = t1.clone().union(t2);
        }
    }
    (t, binds, (pattern, span))
}
