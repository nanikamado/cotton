mod simplify;

pub use self::simplify::{simplify_subtype_rel, TypeVariableMap};
use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        ident_id::IdentId,
        name_id::Name,
        types::{self, SingleTypeConstructor, TypeMatchable},
        types::{Type, TypeUnit, TypeVariable},
        Ast, DataDecl, Expr, ExprWithType, FnArm, Pattern, PatternRestrictions,
        PatternUnit, PatternUnitForRestriction, SubtypeRelations, TypeId,
        TypeWithEnv,
    },
    ast_step4::VariableKind,
    errors::CompileError,
    intrinsics::{IntrinsicConstructor, IntrinsicType, IntrinsicVariable},
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::{multiunzip, Itertools};
use petgraph::{
    algo::kosaraju_scc, graph::NodeIndex, visit::IntoNodeReferences, Graph,
};
use std::{cmp::Reverse, fmt::Display};
use strum::IntoEnumIterator;
use types::TypeConstructor;

#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum VariableId {
    Decl(DeclId),
    IntrinsicVariable(IntrinsicVariable),
    IntrinsicConstructor(IntrinsicConstructor),
}

impl Display for VariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => a.fmt(f),
            VariableId::IntrinsicVariable(a) => a.fmt(f),
            VariableId::IntrinsicConstructor(a) => a.fmt(f),
        }
    }
}

impl std::fmt::Debug for VariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => write!(f, "VariableId({})", a),
            VariableId::IntrinsicVariable(a) => {
                write!(f, "VariableId({})", a)
            }
            VariableId::IntrinsicConstructor(a) => {
                write!(f, "VariableId({})", a)
            }
        }
    }
}

pub struct TypeCheckResult {
    pub resolved_idents: FxHashMap<IdentId, ResolvedIdent>,
    pub global_variable_types: FxHashMap<VariableId, GlobalVariableType>,
    pub local_variable_types: FxHashMap<VariableId, LocalVariableType>,
    pub type_variable_map: TypeVariableMap,
}

pub fn type_check(ast: &Ast) -> Result<TypeCheckResult, CompileError> {
    let mut toplevels: Vec<Toplevel> = Default::default();
    for v in IntrinsicVariable::iter() {
        toplevels.push(Toplevel {
            type_with_env: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicVariable(v),
            name: Name::from_str(v.to_str()),
            implicit_parameter_names: Default::default(),
            variable_kind: VariableKind::Intrinsic,
            fixed_parameters: Default::default(),
        });
    }
    for v in IntrinsicConstructor::iter() {
        toplevels.push(Toplevel {
            type_with_env: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicConstructor(v),
            name: Name::from_str(v.to_str()),
            implicit_parameter_names: Default::default(),
            variable_kind: VariableKind::IntrinsicConstructor,
            fixed_parameters: Default::default(),
        });
    }
    for d in &ast.data_decl {
        let d_type: types::Type = constructor_type(d.clone()).into();
        toplevels.push(Toplevel {
            type_with_env: d_type.into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
            implicit_parameter_names: Default::default(),
            variable_kind: VariableKind::Constructor,
            fixed_parameters: Default::default(),
        });
    }
    let mut resolved_idents = Vec::new();
    let mut subtype_relations = SubtypeRelations::default();
    let mut map = TypeVariableMap::default();
    let mut types_of_local_decls = Vec::new();
    for d in &ast.variable_decl {
        let (mut t, resolved, tod) =
            min_type_with_env(&d.value, &mut subtype_relations, &mut map);
        resolved_idents.extend(resolved);
        types_of_local_decls.extend(
            tod.into_iter()
                .map(|(decl_id, t)| (decl_id, (t, d.decl_id))),
        );
        let type_annotation = if let Some(annotation) = &d.type_annotation {
            t.insert_to_subtype_rels_with_restrictions((
                t.constructor.clone(),
                annotation.fixed.clone(),
            ));
            Some(annotation.unfixed.clone())
        } else {
            None
        };
        let vs: FxHashMap<_, _> = d
            .type_annotation
            .iter()
            .flat_map(|ann| {
                ann.implicit_parameters
                    .iter()
                    .map(|(s, t, decl_id)| (*s, (t, decl_id)))
            })
            .collect();
        let mut suptype_rel = Vec::new();
        t.variable_requirements = t
            .variable_requirements
            .into_iter()
            .filter_map(|mut req| {
                if let Some((t, decl_id)) = vs.get(&req.name) {
                    let (t, _) = (*t).clone().remove_parameters();
                    suptype_rel.push((t, req.required_type.clone()));
                    resolved_idents.push((
                        req.ident,
                        ResolvedIdent {
                            variable_id: VariableId::Decl(**decl_id),
                            implicit_args: Default::default(),
                            variable_kind: VariableKind::Local,
                        },
                    ));
                    None
                } else {
                    req.local_env.extend(vs.iter().map(
                        |(name, (t, decl_id))| {
                            (*name, **decl_id, (**t).clone())
                        },
                    ));
                    Some(req)
                }
            })
            .collect();
        t.subtype_relations.extend(suptype_rel);
        let type_with_env = simplify::simplify_type(
            &mut map,
            TypeWithEnv {
                constructor: SingleTypeConstructor {
                    type_: t.constructor,
                    has_annotation: type_annotation.is_some(),
                },
                variable_requirements: t.variable_requirements,
                subtype_relations: t.subtype_relations,
                pattern_restrictions: t.pattern_restrictions,
                already_considered_relations: t.already_considered_relations,
                fn_apply_dummies: t.fn_apply_dummies,
            },
        )?;
        toplevels.push(Toplevel {
            type_with_env: type_with_env.into(),
            type_annotation,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
            implicit_parameter_names: d
                .type_annotation
                .as_ref()
                .map(|ann| {
                    ann.implicit_parameters
                        .iter()
                        .map(|(name, _, _)| *name)
                        .collect()
                })
                .unwrap_or_default(),
            variable_kind: VariableKind::Global,
            fixed_parameters: d
                .type_annotation
                .as_ref()
                .map(|ann| ann.fixed_parameter_names.clone())
                .unwrap_or_default(),
        });
    }
    for top in &toplevels {
        log::debug!("{:<3} {} : ", top.decl_id, top.name);
        log::debug!("resolved: {:?}", top.resolved_idents);
        if let Some(f) = &top.type_annotation {
            log::debug!("face: {}", f);
            log::debug!("type_with_env: {}", top.type_with_env);
        } else {
            log::debug!("not face: {}", top.type_with_env);
        }
    }
    let (mut resolved_names, types, _rel) = resolve_names(toplevels, &mut map)?;
    // TODO: check _rel
    for (ident_id, ResolvedIdent { variable_id, .. }) in
        resolved_names.iter().sorted_unstable()
    {
        log::debug!("{ident_id} => {variable_id:?}");
    }
    resolved_idents.append(&mut resolved_names);
    let resolved_idents = resolved_idents
        .into_iter()
        .map(
            |(
                ident_id,
                ResolvedIdent {
                    variable_id,
                    implicit_args,
                    variable_kind,
                },
            )| {
                (
                    ident_id,
                    ResolvedIdent {
                        variable_id,
                        implicit_args: implicit_args
                            .into_iter()
                            .map(|(name, t, r)| {
                                (name, map.normalize_type(t), r)
                            })
                            .collect(),
                        variable_kind,
                    },
                )
            },
        )
        .collect();
    // TODO: check subtype_relations
    Ok(TypeCheckResult {
        resolved_idents,
        global_variable_types: types
            .into_iter()
            .map(|(d, t)| {
                (
                    d,
                    t.map_type(|t| lift_recursive_alias(map.normalize_type(t))),
                )
            })
            .collect(),
        local_variable_types: types_of_local_decls
            .into_iter()
            .map(|(d, (t, toplevel))| {
                (
                    d,
                    LocalVariableType {
                        t: lift_recursive_alias(map.normalize_type(t)),
                        toplevel,
                    },
                )
            })
            .collect(),
        type_variable_map: map,
    })
}

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct ResolvedIdent {
    pub variable_id: VariableId,
    pub variable_kind: VariableKind,
    pub implicit_args: Vec<(Name, Type, ResolvedIdent)>,
}

pub type Resolved = Vec<(IdentId, ResolvedIdent)>;

#[derive(Debug, Clone)]
struct Toplevel {
    type_with_env: ast_step2::TypeWithEnv,
    type_annotation: Option<Type>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: Name,
    implicit_parameter_names: Vec<Name>,
    variable_kind: VariableKind,
    fixed_parameters: FxHashMap<TypeUnit, Name>,
}

type TypesOfLocalDeclsVec = Vec<(VariableId, ast_step2::types::Type)>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct GlobalVariableType {
    pub t: Type,
    pub fixed_parameters: FxHashMap<TypeUnit, Name>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LocalVariableType {
    pub t: Type,
    pub toplevel: DeclId,
}

impl GlobalVariableType {
    pub fn map_type<F>(self, mut f: F) -> Self
    where
        F: FnMut(Type) -> Type,
    {
        Self {
            t: self.t.map_type(&mut f),
            fixed_parameters: self.fixed_parameters,
        }
    }
}

type TypesOfGlobalDeclsVec = Vec<(VariableId, GlobalVariableType)>;

fn resolve_names(
    toplevels: Vec<Toplevel>,
    map: &mut TypeVariableMap,
) -> Result<(Resolved, TypesOfGlobalDeclsVec, SubtypeRelations), CompileError> {
    let mut toplevel_graph = Graph::<Toplevel, ()>::new();
    for t in toplevels {
        toplevel_graph.add_node(t);
    }
    let mut toplevle_map: FxHashMap<Name, Vec<NodeIndex>> =
        FxHashMap::default();
    for (i, t) in toplevel_graph.node_references() {
        toplevle_map.entry(t.name).or_default().push(i);
    }
    let edges = toplevel_graph
        .node_references()
        .flat_map(|(from, from_toplevle)| {
            from_toplevle
                .type_with_env
                .variable_requirements
                .iter()
                .flat_map(|req| {
                    toplevle_map
                        .get(&req.name)
                        .unwrap_or_else(|| panic!("{} not found", req.name))
                })
                .map(move |to| (*to, from))
        })
        .collect_vec();
    for (from, to) in edges {
        toplevel_graph.add_edge(from, to, ());
    }
    let toplevel_sccs = kosaraju_scc(&toplevel_graph);
    let mut resolved_variable_map = FxHashMap::default();
    let mut resolved_idents = Vec::new();
    let mut rel = SubtypeRelations::default();
    for scc in toplevel_sccs.into_iter().rev() {
        let unresolved_variables = scc
            .into_iter()
            .map(|i| toplevel_graph[i].clone())
            .collect_vec();
        let mut resolved = resolve_scc(
            unresolved_variables.clone(),
            &resolved_variable_map,
            map,
        )?;
        resolved_idents.append(&mut resolved.0);
        rel = rel.merge(resolved.2);
        for (toplevel, improved_type) in
            unresolved_variables.into_iter().zip(resolved.1)
        {
            log::debug!(
                "improved type of {}:\n{}",
                toplevel.name,
                improved_type
            );
            resolved_variable_map
                .entry(toplevel.name)
                .or_default()
                .push(Toplevel {
                    type_with_env: improved_type.into(),
                    ..toplevel
                });
        }
    }
    let types = resolved_variable_map
        .into_iter()
        .flat_map(|(_, toplevels)| {
            toplevels.into_iter().map(|t| {
                (
                    t.decl_id,
                    GlobalVariableType {
                        t: t.type_annotation
                            .unwrap_or(t.type_with_env.constructor),
                        fixed_parameters: t.fixed_parameters,
                    },
                )
            })
        })
        .collect();
    Ok((resolved_idents, types, rel))
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SccTypeConstructor(Vec<SingleTypeConstructor>);

impl Display for SccTypeConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.0.iter().join(", "))?;
        write!(f, "]")
    }
}

impl Type {
    fn argument_tuple_from_arguments(ts: Vec<Self>) -> Self {
        let mut new_ts = Type::label_from_str("()");
        for t in ts.into_iter().rev() {
            new_ts = TypeUnit::Tuple(t, new_ts).into();
        }
        new_ts
    }

    fn arguments_from_argument_tuple(self) -> Vec<Self> {
        use TypeMatchable::*;
        match self.matchable() {
            Tuple(a1, a2) => std::iter::once(a1)
                .chain(a2.arguments_from_argument_tuple())
                .collect(),
            Const { id, .. }
                if id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            t => {
                panic!("expected AT or Unit but got {}", Type::from(t))
            }
        }
    }

    pub fn remove_parameters(mut self) -> (Self, Vec<TypeVariable>) {
        let mut parameters = Vec::new();
        let t = loop {
            match self.matchable() {
                TypeMatchable::TypeLevelFn(t) => {
                    let v = TypeVariable::new();
                    self = t.replace_num(
                        TypeVariable::RecursiveIndex(0),
                        &TypeUnit::Variable(v).into(),
                    );
                    parameters.push(v);
                }
                t => {
                    break t;
                }
            }
        };
        (t.into(), parameters)
    }
}

impl PatternUnitForRestriction {
    fn argument_tuple_from_arguments(ps: Vec<Self>) -> Self {
        let mut new_p = PatternUnitForRestriction::Const {
            id: TypeId::Intrinsic(IntrinsicType::Unit),
        };
        for p in ps.iter().rev() {
            new_p = PatternUnitForRestriction::Tuple(
                p.clone().into(),
                new_p.into(),
            );
        }
        new_p
    }

    fn arguments_from_argument_tuple(self) -> Vec<Self> {
        use PatternUnitForRestriction::*;
        match self {
            Tuple(a1, a2) => std::iter::once(*a1)
                .chain(a2.arguments_from_argument_tuple())
                .collect(),
            Const { id, .. }
                if id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            _ => panic!(),
        }
    }

    fn arguments_from_argument_tuple_ref(&self) -> Vec<&Self> {
        use PatternUnitForRestriction::*;
        match self {
            Tuple(a1, a2) => std::iter::once(&**a1)
                .chain(a2.arguments_from_argument_tuple_ref())
                .collect(),
            Const { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            _ => panic!(),
        }
    }
}

impl TypeConstructor for SccTypeConstructor {
    fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        self.all_type_variables_vec().into_iter().collect()
    }

    fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        self.0
            .iter()
            .flat_map(TypeConstructor::all_type_variables_vec)
            .collect()
    }

    fn replace_num(self, from: TypeVariable, to: &Type) -> Self {
        self.replace_num_with_update_flag(from, to, 0).0
    }

    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        let mut updated = false;
        let t = self.map_type(|t| {
            let (t, u) =
                t.replace_num_with_update_flag(from, to, recursive_alias_depth);
            updated = u;
            t
        });
        (t, updated)
    }

    fn covariant_type_variables(&self) -> Vec<TypeVariable> {
        self.0
            .iter()
            .flat_map(TypeConstructor::covariant_type_variables)
            .collect()
    }

    fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        self.0
            .iter()
            .flat_map(TypeConstructor::contravariant_type_variables)
            .collect()
    }

    fn find_recursive_alias(&self) -> Option<&Type> {
        self.0
            .iter()
            .find_map(TypeConstructor::find_recursive_alias)
    }

    fn replace_type(self, from: &TypeUnit, to: &TypeUnit) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_type(from, to))
                .collect(),
        )
    }

    fn replace_type_union(self, from: &Type, to: &TypeUnit) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_type_union(from, to))
                .collect(),
        )
    }

    fn replace_type_union_with_update_flag(
        self,
        from: &Type,
        to: &TypeUnit,
        recursive_alias_depth: usize,
    ) -> (Self, bool) {
        let mut updated = false;
        let t = self.map_type(|t| {
            let (t, u) = t.replace_type_union_with_update_flag(
                from,
                to,
                recursive_alias_depth,
            );
            updated = u;
            t
        });
        (t, updated)
    }

    fn map_type<F: FnMut(Type) -> Type>(self, mut f: F) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|mut t| {
                    t.type_ = f(t.type_);
                    t
                })
                .collect(),
        )
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.0.iter().any(|s| s.contains_variable(v))
    }
}

/// Resolves names in strongly connected declarations.
/// Returns the resolved names and improved type of each declaration.
fn resolve_scc(
    scc: Vec<Toplevel>,
    resolved_variable_map: &FxHashMap<Name, Vec<Toplevel>>,
    map: &mut TypeVariableMap,
) -> Result<(Resolved, Vec<Type>, SubtypeRelations), CompileError> {
    // Merge the declarations in a scc to treate them as if they are one declaration,
    let mut resolved_idents = Vec::new();
    let mut name_vec = Vec::new();
    let mut variable_requirements = Vec::new();
    let mut subtype_relations = SubtypeRelations::default();
    let mut pattern_restrictions = PatternRestrictions::default();
    let mut types = Vec::new();
    for t in &scc {
        name_vec.push(t.name);
        variable_requirements
            .append(&mut t.type_with_env.variable_requirements.clone());
        subtype_relations.extend(t.type_with_env.subtype_relations.clone());
        types.push(SingleTypeConstructor {
            type_: t.type_with_env.constructor.clone(),
            has_annotation: t.type_annotation.is_some(),
        });
        pattern_restrictions
            .extend(t.type_with_env.pattern_restrictions.clone())
    }
    let names_in_scc: FxHashSet<_> = name_vec.iter().copied().collect();
    log::debug!("name of unresolved: {:?}", names_in_scc);
    // The order of resolving is important.
    // Requirements that are easier to solve should be solved earlier.
    variable_requirements.sort_unstable_by_key(|req| {
        Reverse(difficulty_of_resolving(
            req.name,
            &names_in_scc,
            resolved_variable_map,
        ))
    });
    let mut unresolved_type = TypeWithEnv {
        constructor: SccTypeConstructor(types),
        variable_requirements,
        subtype_relations,
        pattern_restrictions,
        already_considered_relations: Default::default(),
        fn_apply_dummies: Default::default(),
    };
    // Recursions are not resolved in this loop.
    while let Some(req) = unresolved_type.variable_requirements.pop() {
        if names_in_scc.contains(&req.name) {
            unresolved_type.variable_requirements.push(req);
            // Skipping the resolveing of recursion.
            break;
        }
        let (satisfied, es) = find_satisfied_types(
            &req,
            &unresolved_type,
            resolved_variable_map,
            map,
            &names_in_scc,
        );
        let satisfied = get_one_satisfied(satisfied, es, req.name)?;
        resolved_idents.push((
            req.ident,
            ResolvedIdent {
                variable_id: satisfied.id_of_satisfied_variable,
                implicit_args: satisfied.implicit_args,
                variable_kind: satisfied.variable_kind,
            },
        ));
        *map = satisfied.map;
        unresolved_type = satisfied.type_of_improved_decl;
    }
    // Resolve recursive requirements.
    let (mut resolved, improved_types) = resolve_recursion_in_scc(
        unresolved_type,
        &scc,
        resolved_variable_map,
        map,
        &names_in_scc,
    )?;
    resolved_idents.append(&mut resolved);
    let variable_requirements = improved_types.variable_requirements;
    let subtype_relation = improved_types.subtype_relations.clone();
    Ok((
        resolved_idents,
        improved_types
            .constructor
            .0
            .into_iter()
            .map(|t| {
                let t = simplify::simplify_type(
                    map,
                    TypeWithEnv {
                        constructor: t.type_,
                        variable_requirements: variable_requirements.clone(),
                        subtype_relations: subtype_relation.clone(),
                        pattern_restrictions: improved_types
                            .pattern_restrictions
                            .clone(),
                        already_considered_relations: improved_types
                            .already_considered_relations
                            .clone(),
                        fn_apply_dummies: improved_types
                            .fn_apply_dummies
                            .clone(),
                    },
                )
                .unwrap();
                debug_assert_eq!(
                    t,
                    simplify::simplify_type(map, t.clone()).unwrap()
                );
                // TODO: check remaining pattern_restrictions
                let vs = t
                    .constructor
                    .all_type_variables()
                    .into_iter()
                    .filter(|v| !v.is_recursive_index())
                    .collect_vec();
                if vs.is_empty() {
                    t.constructor
                } else {
                    assert!(t.variable_requirements.is_empty());
                    let mut t = if t.subtype_relations.is_empty() {
                        t.constructor
                    } else {
                        TypeUnit::Restrictions {
                            t: t.constructor,
                            variable_requirements: Vec::new(),
                            subtype_relations: t.subtype_relations,
                        }
                        .into()
                    };
                    for (i, v) in vs.iter().enumerate() {
                        t = t.replace_num(
                            *v,
                            &TypeUnit::Variable(TypeVariable::RecursiveIndex(
                                i,
                            ))
                            .into(),
                        );
                    }
                    for _ in 0..vs.len() {
                        t = TypeUnit::TypeLevelFn(t).into();
                    }
                    t
                }
            })
            .collect(),
        improved_types.subtype_relations,
    ))
}

#[derive(Debug, PartialEq, Eq)]
struct Difficulty {
    same_scc: bool,
    implicit_parameters_are_recurring: bool,
    number_of_candidates: usize,
    diff_of_implicit_parameter_required_by_candidates: Option<Box<Difficulty>>,
}

fn difficulty_of_resolving(
    req_name: Name,
    names_in_scc: &FxHashSet<Name>,
    resolved_variable_map: &FxHashMap<Name, Vec<Toplevel>>,
) -> Difficulty {
    fn difficulty_of_resolving_rec(
        req_name: Name,
        names_in_scc: &FxHashSet<Name>,
        resolved_variable_map: &FxHashMap<Name, Vec<Toplevel>>,
        mut visited_names: FxHashSet<Name>,
    ) -> Difficulty {
        let implicit_parameters_are_recurring =
            visited_names.contains(&req_name);
        visited_names.insert(req_name);
        Difficulty {
            same_scc: names_in_scc.contains(&req_name),
            implicit_parameters_are_recurring,
            diff_of_implicit_parameter_required_by_candidates:
                if implicit_parameters_are_recurring {
                    None
                } else {
                    resolved_variable_map
                        .get(&req_name)
                        .and_then(|v| {
                            v.iter()
                                .flat_map(|d| {
                                    d.implicit_parameter_names.iter().map(
                                        |name| {
                                            difficulty_of_resolving_rec(
                                                *name,
                                                names_in_scc,
                                                resolved_variable_map,
                                                visited_names.clone(),
                                            )
                                        },
                                    )
                                })
                                .max()
                        })
                        .map(Box::new)
                },
            number_of_candidates: resolved_variable_map
                .get(&req_name)
                .map(|v| v.len())
                .unwrap_or_default(),
        }
    }
    difficulty_of_resolving_rec(
        req_name,
        names_in_scc,
        resolved_variable_map,
        FxHashSet::default(),
    )
}

impl Ord for Difficulty {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            self.same_scc,
            self.implicit_parameters_are_recurring,
            self.number_of_candidates != 0,
            &self.diff_of_implicit_parameter_required_by_candidates,
            self.number_of_candidates,
        )
            .cmp(&(
                other.same_scc,
                other.implicit_parameters_are_recurring,
                other.number_of_candidates != 0,
                &other.diff_of_implicit_parameter_required_by_candidates,
                other.number_of_candidates,
            ))
    }
}

impl PartialOrd for Difficulty {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

struct SatisfiedType<T> {
    type_of_satisfied_variable: Type,
    id_of_satisfied_variable: VariableId,
    variable_kind: VariableKind,
    type_of_improved_decl: T,
    implicit_args: Vec<(Name, Type, ResolvedIdent)>,
    map: TypeVariableMap,
}

trait CandidatesProvider: Copy {
    type T: Iterator<Item = Candidate>;
    fn get_candidates(self, req_name: Name) -> Self::T;
}

impl CandidatesProvider for &FxHashMap<Name, Vec<Toplevel>> {
    type T = std::vec::IntoIter<Candidate>;

    fn get_candidates(self, req_name: Name) -> Self::T {
        self.get(&req_name)
            .into_iter()
            .flatten()
            .cloned()
            .map(|t| Candidate { candidate: t })
            .collect_vec()
            .into_iter()
    }
}

#[derive(Debug, Clone, Copy)]
struct CandidatesProviderWithFn<'b, F: FnMut(usize) -> Candidate> {
    scc_map: &'b FxHashMap<Name, Vec<usize>>,
    f: F,
}

impl<'b, F: FnMut(usize) -> Candidate + Copy> CandidatesProvider
    for CandidatesProviderWithFn<'b, F>
{
    type T = std::iter::Map<std::vec::IntoIter<usize>, F>;

    fn get_candidates(self, req_name: Name) -> Self::T {
        self.scc_map
            .get(&req_name)
            .iter()
            .copied()
            .flatten()
            .copied()
            .collect_vec()
            .into_iter()
            .map(self.f)
    }
}

#[derive(Debug, Clone)]
struct Candidate {
    candidate: Toplevel,
}

#[derive(Debug, Clone, Copy)]
struct CandidatesProviderForScc<'b, F: FnMut(usize) -> Candidate> {
    candidates_provider_with_fn: CandidatesProviderWithFn<'b, F>,
    normal_map: &'b FxHashMap<Name, Vec<Toplevel>>,
}

impl<'b, F: FnMut(usize) -> Candidate + Copy> CandidatesProvider
    for CandidatesProviderForScc<'b, F>
{
    type T = std::iter::Chain<
        std::vec::IntoIter<Candidate>,
        std::iter::Map<std::vec::IntoIter<usize>, F>,
    >;

    fn get_candidates(self, req_name: Name) -> Self::T {
        self.normal_map
            .get_candidates(req_name)
            .chain(self.candidates_provider_with_fn.get_candidates(req_name))
    }
}

fn find_satisfied_types<T: TypeConstructor, C: CandidatesProvider>(
    req: &VariableRequirement,
    type_of_unresolved_decl: &TypeWithEnv<T>,
    resolved_variable_map: C,
    map: &TypeVariableMap,
    names_in_scc: &FxHashSet<Name>,
) -> (Vec<SatisfiedType<TypeWithEnv<T>>>, Vec<CompileError>) {
    log::trace!("type_of_unresolved_decl:");
    log::trace!("{}", type_of_unresolved_decl);
    log::trace!("required_type : {}", req.required_type);
    resolved_variable_map
        .get_candidates(req.name)
        .map(|Candidate { candidate }| {
            let mut t = type_of_unresolved_decl.clone();
            let mut cand_t = if let Some(face) = candidate.type_annotation {
                face.into()
            } else {
                candidate.type_with_env
            };
            let mut map = map.clone();
            log::debug!("req: {}", req.required_type);
            log::debug!("~~ {} : {}", candidate.name, cand_t);
            let mut implicit_args = Vec::new();
            let mut resolved_implicit_args = FxHashMap::default();
            let type_args;
            (cand_t.constructor, type_args) =
                cand_t.constructor.remove_parameters();
            cand_t.constructor = match cand_t.constructor.matchable() {
                TypeMatchable::Restrictions {
                    t: constructor,
                    variable_requirements,
                    subtype_relations,
                } => {
                    for (interface_v_name, interface_v_t) in
                        variable_requirements
                    {
                        let arg = IdentId::new();
                        implicit_args.push((
                            interface_v_name,
                            interface_v_t.clone(),
                            arg,
                        ));
                        if let Some((_, decl_id, found_t)) = req
                            .local_env
                            .iter()
                            .find(|(name, _, _)| interface_v_name == *name)
                        {
                            resolved_implicit_args.insert(
                                arg,
                                ResolvedIdent {
                                    variable_id: VariableId::Decl(*decl_id),
                                    implicit_args: Default::default(),
                                    variable_kind: VariableKind::Local,
                                },
                            );
                            map.insert_type(
                                &mut t.subtype_relations,
                                interface_v_t,
                                found_t.clone(),
                            );
                        } else {
                            cand_t.variable_requirements.push(
                                VariableRequirement {
                                    name: interface_v_name,
                                    required_type: interface_v_t,
                                    ident: arg,
                                    local_env: req.local_env.clone(),
                                },
                            );
                        }
                    }
                    t.subtype_relations.extend(subtype_relations);
                    constructor
                }
                t => t.into(),
            };
            let (required_type, ps_from_rec) =
                req.required_type.clone().remove_parameters();
            for (a, b) in type_args.iter().zip(ps_from_rec) {
                map.insert(
                    &mut t.subtype_relations,
                    *a,
                    TypeUnit::Variable(b).into(),
                );
            }
            t.subtype_relations.add_subtype_rel(
                cand_t.constructor.clone(),
                required_type.clone(),
            );
            t.subtype_relations
                .add_subtype_rel(required_type, cand_t.constructor.clone());
            t.subtype_relations
                .add_subtype_rels(cand_t.subtype_relations);
            t.variable_requirements
                .extend(cand_t.variable_requirements.clone());
            let decl_id = candidate.decl_id;
            match simplify::simplify_type(&mut map, t) {
                Ok(mut type_of_improved_decl) => {
                    while let Some(req) = cand_t.variable_requirements.pop() {
                        if names_in_scc.contains(&req.name) {
                            type_of_improved_decl
                                .variable_requirements
                                .push(req);
                            // Skipping the resolveing of recursion.
                            panic!();
                            // break;
                        }
                        let (satisfied, es) = find_satisfied_types(
                            &req,
                            &type_of_improved_decl,
                            resolved_variable_map,
                            &map,
                            names_in_scc,
                        );
                        let satisfied =
                            get_one_satisfied(satisfied, es, req.name)?;
                        resolved_implicit_args.insert(
                            req.ident,
                            ResolvedIdent {
                                variable_id: satisfied.id_of_satisfied_variable,
                                implicit_args: satisfied.implicit_args,
                                variable_kind: satisfied.variable_kind,
                            },
                        );
                        map = satisfied.map;
                        type_of_improved_decl = satisfied.type_of_improved_decl;
                    }
                    Ok(SatisfiedType {
                        id_of_satisfied_variable: decl_id,
                        type_of_improved_decl,
                        implicit_args: implicit_args
                            .into_iter()
                            .map(|(name, t, ident_id)| {
                                (
                                    name,
                                    t,
                                    resolved_implicit_args[&ident_id].clone(),
                                )
                            })
                            .collect(),
                        type_of_satisfied_variable: cand_t.constructor,
                        map,
                        variable_kind: candidate.variable_kind,
                    })
                }
                Err(r) => Err(r),
            }
        })
        .partition_result()
}

fn get_one_satisfied<T: Display>(
    satisfied: Vec<SatisfiedType<T>>,
    es: Vec<CompileError>,
    variable_name: Name,
) -> Result<SatisfiedType<T>, CompileError> {
    match satisfied.len() {
        0 => Err(CompileError::NoSuitableVariable {
            name: variable_name,
            reason: es,
        }),
        1 => Ok(satisfied.into_iter().next().unwrap()),
        _ => Err(CompileError::ManyCandidates {
            satisfied: satisfied
                .iter()
                .map(|s| {
                    format!(
                        "{} : {}",
                        s.id_of_satisfied_variable, s.type_of_improved_decl
                    )
                })
                .collect(),
        }),
    }
}

/// The reterned `TypeWithEnv` does not contain variable_requirements, but contains subtype relationship.
fn resolve_recursion_in_scc(
    mut scc: TypeWithEnv<SccTypeConstructor>,
    toplevels: &[Toplevel],
    resolved_variable_map: &FxHashMap<Name, Vec<Toplevel>>,
    map: &mut TypeVariableMap,
    names_in_scc: &FxHashSet<Name>,
) -> Result<(Resolved, TypeWithEnv<SccTypeConstructor>), CompileError> {
    let mut scc_map: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
    for (i, t) in toplevels.iter().enumerate() {
        scc_map.entry(t.name).or_default().push(i);
    }
    let mut resolved_idents = Vec::new();
    while let Some(req) = scc.variable_requirements.pop() {
        let (satisfied, es) = find_satisfied_types(
            &req,
            &scc,
            CandidatesProviderForScc {
                candidates_provider_with_fn: CandidatesProviderWithFn {
                    scc_map: &scc_map,
                    f: |j| Candidate {
                        candidate: Toplevel {
                            type_with_env: scc.constructor.0[j]
                                .type_
                                .clone()
                                .into(),
                            ..toplevels[j].clone()
                        },
                    },
                },
                normal_map: resolved_variable_map,
            },
            map,
            names_in_scc,
        );
        let satisfied = get_one_satisfied(satisfied, es, req.name)?;
        *map = satisfied.map;
        map.insert_type(
            &mut scc.subtype_relations,
            req.required_type,
            satisfied.type_of_satisfied_variable,
        );
        resolved_idents.push((
            req.ident,
            ResolvedIdent {
                variable_id: satisfied.id_of_satisfied_variable,
                implicit_args: satisfied.implicit_args,
                variable_kind: satisfied.variable_kind,
            },
        ));
        scc = satisfied.type_of_improved_decl;
    }
    Ok((resolved_idents, scc))
}

fn constructor_type(d: DataDecl) -> TypeUnit {
    let fields: Vec<_> = d
        .fields
        .iter()
        .enumerate()
        .map(|(i, _t)| {
            TypeUnit::Variable(TypeVariable::RecursiveIndex(i)).into()
        })
        .rev()
        .collect();
    let mut t = TypeUnit::Tuple(
        TypeUnit::Const {
            id: TypeId::DeclId(d.decl_id),
        }
        .into(),
        Type::argument_tuple_from_arguments(fields.clone()),
    );
    for field in fields.into_iter().rev() {
        t = TypeUnit::Fn(field, t.into())
    }
    for _ in 0..d.fields.len() {
        t = TypeUnit::TypeLevelFn(t.into())
    }
    t
}

fn min_type_with_env(
    (expr, type_variable): &ExprWithType<TypeVariable>,
    subtype_relations: &mut SubtypeRelations,
    map: &mut TypeVariableMap,
) -> (ast_step2::TypeWithEnv, Resolved, TypesOfLocalDeclsVec) {
    match expr {
        Expr::Lambda(arms) => {
            let (
                arm_types,
                restrictions,
                variable_requirements,
                subtype_relation,
                resolved_idents,
                pattern_restrictions,
                types_of_decls,
            ): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = multiunzip(
                arms.iter()
                    .map(|arm| arm_min_type(arm, subtype_relations, map)),
            );
            let resolved_idents = resolved_idents.concat();
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
            let mut pattern_restrictions = pattern_restrictions.concat();
            let restrictions = restrictions
                .into_iter()
                .map(PatternUnitForRestriction::argument_tuple_from_arguments)
                .collect();
            pattern_restrictions.push((
                Type::argument_tuple_from_arguments(arg_types),
                restrictions,
            ));
            map.insert(subtype_relations, *type_variable, constructor.clone());
            (
                ast_step2::TypeWithEnv {
                    constructor,
                    variable_requirements: variable_requirements.concat(),
                    subtype_relations: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                    fn_apply_dummies: Default::default(),
                },
                resolved_idents,
                types_of_decls.concat(),
            )
        }
        Expr::Number(_) => {
            let t = Type::from_str("I64");
            map.insert(subtype_relations, *type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::StrLiteral(_) => {
            let t = Type::from_str("String");
            map.insert(subtype_relations, *type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::Ident { name, ident_id, .. } => {
            let t: Type = TypeUnit::Variable(*type_variable).into();
            (
                ast_step2::TypeWithEnv {
                    constructor: t.clone(),
                    variable_requirements: vec![VariableRequirement {
                        name: *name,
                        required_type: t,
                        ident: *ident_id,
                        local_env: Default::default(),
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
        Expr::Call(f, a) => {
            let (f_t, resolved1, types_of_decls_f) =
                min_type_with_env(f, subtype_relations, map);
            let (a_t, resolved2, types_of_decls_a) =
                min_type_with_env(a, subtype_relations, map);
            let b: types::Type = TypeUnit::Variable(*type_variable).into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn: Type = TypeUnit::Fn(c.clone(), b.clone()).into();
            // f < c -> b
            let f_sub_cb = [(f_t.constructor.clone(), cb_fn.clone())]
                .iter()
                .cloned()
                .collect();
            // c -> b < f
            let cb_sub_f = [(cb_fn, f_t.constructor)].iter().cloned().collect();
            // a < c
            let a_sub_c = [(a_t.constructor, c)].iter().cloned().collect();
            (
                ast_step2::TypeWithEnv {
                    constructor: b,
                    variable_requirements: [
                        f_t.variable_requirements,
                        a_t.variable_requirements,
                    ]
                    .concat(),
                    subtype_relations: vec![
                        f_sub_cb,
                        cb_sub_f,
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
                    let (t, resolved, mut tod) =
                        min_type_with_env(e, &mut subtype_relations, map);
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
                ast_step2::TypeWithEnv {
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct VariableRequirement {
    pub name: Name,
    pub required_type: Type,
    pub ident: IdentId,
    pub local_env: Vec<(Name, DeclId, Type)>,
}

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type(
    arm: &FnArm<TypeVariable>,
    subtype_relations: &mut SubtypeRelations,
    map: &mut TypeVariableMap,
) -> (
    Vec<types::Type>,
    Vec<PatternUnitForRestriction>,
    Vec<VariableRequirement>,
    SubtypeRelations,
    Resolved,
    PatternRestrictions,
    TypesOfLocalDeclsVec,
) {
    let (body_type, mut resolved_idents, mut types_of_decls) =
        min_type_with_env(&arm.expr, subtype_relations, map);
    let (mut ts, bindings, patterns): (Vec<_>, Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).multiunzip();
    ts.push(body_type.constructor);
    let bindings: FxHashMap<Name, (DeclId, types::Type)> = bindings
        .into_iter()
        .flatten()
        .inspect(|(_, (decl_id, t))| {
            types_of_decls.push((VariableId::Decl(*decl_id), t.clone()));
        })
        .collect();
    let mut variable_requirements = Vec::new();
    let mut subtype_requirement = Vec::new();
    for mut p in body_type.variable_requirements.into_iter() {
        if let Some(a) = bindings.get(&p.name) {
            subtype_requirement.push((a.1.clone(), p.required_type.clone()));
            subtype_requirement.push((p.required_type, a.1.clone()));
            resolved_idents.push((
                p.ident,
                ResolvedIdent {
                    variable_id: VariableId::Decl(a.0),
                    implicit_args: Vec::new(),
                    variable_kind: VariableKind::Local,
                },
            ));
        } else {
            p.local_env.extend(
                bindings
                    .iter()
                    .map(|(name, (decl_id, t))| (*name, *decl_id, t.clone())),
            );
            variable_requirements.push(p);
        }
    }
    (
        ts,
        patterns,
        variable_requirements,
        {
            let mut tmp = body_type.subtype_relations;
            tmp.extend(&mut subtype_requirement.into_iter());
            tmp
        },
        resolved_idents,
        body_type.pattern_restrictions,
        types_of_decls,
    )
}

fn pattern_unit_to_type(
    p: &PatternUnit<TypeVariable>,
) -> (
    types::Type,
    FxHashMap<Name, (DeclId, types::Type)>,
    PatternUnitForRestriction,
) {
    use PatternUnit::*;
    match p {
        I64(_) => (
            Type::from_str("I64"),
            Default::default(),
            PatternUnitForRestriction::I64,
        ),
        Str(_) => (
            Type::from_str("String"),
            Default::default(),
            PatternUnitForRestriction::Str,
        ),
        Constructor { id, args, .. } => {
            let (types, bindings, pattern_restrictions): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = args.iter().map(pattern_to_type).multiunzip();
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
                    .into(),
                ),
            )
        }
        Binder(name, decl_id, t) => (
            TypeUnit::Variable(*t).into(),
            vec![(*name, (*decl_id, TypeUnit::Variable(*t).into()))]
                .into_iter()
                .collect(),
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
        TypeRestriction(_p, _t) => {
            // let (_, binds) = pattern_to_type(p);
            // (t.clone(), binds)
            unimplemented!()
        }
    }
}

fn pattern_to_type(
    p: &Pattern<TypeVariable>,
) -> (
    types::Type,
    FxHashMap<Name, (DeclId, types::Type)>,
    PatternUnitForRestriction,
) {
    if p.len() >= 2 {
        unimplemented!()
    }
    let mut ps = p.iter();
    let first_p = ps.next().unwrap();
    let (mut t, mut binds, pattern) = pattern_unit_to_type(first_p);
    for p in ps {
        let (t_, binds_, _pattern_) = pattern_unit_to_type(p);
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
    (t, binds, pattern)
}
