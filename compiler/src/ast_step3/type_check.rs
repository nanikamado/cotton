mod min_type;
mod simplify;

use self::min_type::min_type_with_env;
pub use self::simplify::{
    simplify_subtype_rel, unwrap_recursive_alias, TypeVariableMap,
};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::merge_span;
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::{
    self, unwrap_or_clone, SingleTypeConstructor, Type, TypeMatchable,
    TypeUnit, TypeVariable,
};
use crate::ast_step2::{
    self, Ast, DataDecl, PatternRestrictions, PatternUnitForRestriction,
    RelOrigin, SubtypeRelations, TypeId,
};
use crate::errors::CompileError;
use crate::intrinsics::{
    IntrinsicConstructor, IntrinsicType, IntrinsicVariable,
};
use crate::TypeMatchableRef;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use parser::Span;
use petgraph::algo::kosaraju_scc;
use petgraph::graph::NodeIndex;
use petgraph::visit::IntoNodeReferences;
use petgraph::Graph;
use std::cmp::Reverse;
use std::collections::BTreeMap;
use std::fmt::Display;
use strum::IntoEnumIterator;
use types::TypeConstructor;

const IMPLICIT_PARAMETER_RECURSION_LIMIT: usize = 10;

#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum VariableId {
    Global(DeclId),
    Local(DeclId),
    Constructor(DeclId),
    IntrinsicVariable(IntrinsicVariable),
    IntrinsicConstructor(IntrinsicConstructor),
    FieldAccessor { constructor: DeclId, field: usize },
}

impl Display for VariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableId::Global(a) => a.fmt(f),
            VariableId::IntrinsicVariable(a) => a.fmt(f),
            VariableId::IntrinsicConstructor(a) => a.fmt(f),
            VariableId::FieldAccessor { field, .. } => write!(f, "_{field}"),
            VariableId::Local(a) => a.fmt(f),
            VariableId::Constructor(a) => a.fmt(f),
        }
    }
}

impl std::fmt::Debug for VariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableId::Global(a) => write!(f, "Global({})", a),
            VariableId::IntrinsicVariable(a) => {
                write!(f, "Intrinsic({})", a)
            }
            VariableId::IntrinsicConstructor(a) => {
                write!(f, "IntrinsicConstructor({})", a)
            }
            VariableId::FieldAccessor { constructor, field } => {
                write!(f, "FieldAccessor({constructor}, {field})")
            }
            VariableId::Local(a) => {
                write!(f, "Local({a})")
            }
            VariableId::Constructor(a) => write!(f, "Constructor({a})"),
        }
    }
}

pub struct TypeCheckResult {
    pub resolved_idents: FxHashMap<IdentId, ResolvedIdent>,
    pub global_variable_types: FxHashMap<VariableId, GlobalVariableType>,
    pub local_variable_types: FxHashMap<VariableId, LocalVariableType>,
    pub type_variable_map: TypeVariableMap,
}

pub fn type_check(
    ast: &Ast,
    token_map: &mut TokenMap,
    imports: &mut Imports,
) -> Result<TypeCheckResult, CompileError> {
    let mut toplevels: Vec<Toplevel> = Default::default();
    for v in IntrinsicVariable::iter() {
        toplevels.push(Toplevel {
            type_with_env: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicVariable(v),
            name: Name::from_str_intrinsic(v.to_str()),
            fixed_parameters: Default::default(),
        });
    }
    for v in IntrinsicConstructor::iter() {
        toplevels.push(Toplevel {
            type_with_env: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicConstructor(v),
            name: Name::from_str_intrinsic(v.to_str()),
            fixed_parameters: Default::default(),
        });
    }
    for d in &ast.data_decl {
        let d_type: types::Type = constructor_type(d).into();
        toplevels.push(Toplevel {
            type_with_env: d_type.into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Constructor(d.decl_id),
            name: d.name,
            fixed_parameters: Default::default(),
        });
        for (i, f) in d.fields.iter().enumerate() {
            let t = accessor_type(d, i);
            toplevels.push(Toplevel {
                type_with_env: Type::from(t).into(),
                type_annotation: None,
                resolved_idents: Default::default(),
                decl_id: VariableId::FieldAccessor {
                    constructor: d.decl_id,
                    field: i,
                },
                name: f.name,
                fixed_parameters: Default::default(),
            });
        }
    }
    let mut resolved_idents = Vec::new();
    let mut map = TypeVariableMap::default();
    let mut types_of_local_decls = Vec::new();
    let mut candidates_from_implicit_parameters: FxHashMap<
        VariableId,
        Candidate,
    > = FxHashMap::default();
    for d in &ast.variable_decl {
        let mut candidates_from_implicit_parameters_str: FxHashMap<
            &str,
            Vec<DeclId>,
        > = Default::default();
        if let Some(a) = &d.type_annotation {
            for (name, t, decl_id) in &a.implicit_parameters {
                candidates_from_implicit_parameters_str
                    .entry(name)
                    .or_default()
                    .push(*decl_id);
                let variable_id = VariableId::Local(*decl_id);
                candidates_from_implicit_parameters.insert(
                    variable_id,
                    Candidate {
                        type_: (*t).clone().into(),
                        variable_id,
                    },
                );
            }
        }
        let (mut t, resolved, tod) = min_type_with_env(
            &d.value,
            d.name.split().unwrap().0,
            &mut map,
            imports,
            token_map,
            &candidates_from_implicit_parameters_str,
        )?;
        resolved_idents.extend(resolved);
        types_of_local_decls.extend(
            tod.into_iter()
                .map(|(decl_id, t)| (decl_id, (t, d.decl_id))),
        );
        let type_annotation = if let Some(annotation) = &d.type_annotation {
            t.insert_to_subtype_rels_with_restrictions((
                t.constructor.clone(),
                annotation.fixed.clone(),
                RelOrigin {
                    left: t.constructor.clone(),
                    right: annotation.fixed.clone(),
                    span: d.value.2.clone(),
                },
            ));
            Some(annotation.unfixed.clone())
        } else {
            None
        };
        let type_with_env = simplify::simplify_type(
            &mut map,
            ast_step2::TypeWithEnv {
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
            decl_id: VariableId::Global(d.decl_id),
            name: d.name,
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
    let (mut resolved_names, types, _rel) = resolve_names(
        toplevels,
        imports,
        &mut map,
        &candidates_from_implicit_parameters,
    )?;
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
    pub implicit_args: Vec<(Name, Type, IdentId)>,
}

pub type Resolved = Vec<(IdentId, ResolvedIdent)>;

#[derive(Debug, Clone)]
struct Toplevel {
    type_with_env: ast_step2::TypeWithEnv,
    type_annotation: Option<Type>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: Name,
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
    imports: &mut Imports,
    map: &mut TypeVariableMap,
    candidates_from_implicit_parameters: &FxHashMap<VariableId, Candidate>,
) -> Result<(Resolved, TypesOfGlobalDeclsVec, SubtypeRelations), CompileError> {
    let mut toplevel_graph = Graph::<Toplevel, ()>::new();
    for t in toplevels {
        toplevel_graph.add_node(t);
    }
    let mut toplevel_map: FxHashMap<VariableId, Vec<NodeIndex>> =
        FxHashMap::default();
    for (i, t) in toplevel_graph.node_references() {
        toplevel_map.entry(t.decl_id).or_default().push(i);
    }
    let edges = toplevel_graph
        .node_references()
        .flat_map(|(from, from_toplevel)| {
            from_toplevel
                .type_with_env
                .variable_requirements
                .iter()
                .flat_map(|req| {
                    req.name.iter().flat_map(|name| {
                        toplevel_map.get(name).into_iter().flatten()
                    })
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
            candidates_from_implicit_parameters,
            imports,
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
            resolved_variable_map.insert(
                toplevel.decl_id,
                Toplevel {
                    type_with_env: improved_type.into(),
                    ..toplevel
                },
            );
        }
    }
    let types = resolved_variable_map
        .into_values()
        .map(|t| {
            (
                t.decl_id,
                GlobalVariableType {
                    t: t.type_annotation.unwrap_or(t.type_with_env.constructor),
                    fixed_parameters: t.fixed_parameters,
                },
            )
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

    pub fn arguments_from_argument_tuple_ref(&self) -> Vec<&Self> {
        use TypeMatchableRef::*;
        match self.matchable_ref() {
            Tuple(a1, a2) => std::iter::once(a1)
                .chain(a2.arguments_from_argument_tuple_ref())
                .collect(),
            Const { id, .. }
                if id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            t => {
                panic!("expected AT or Unit but got {:?}", t)
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
    fn argument_tuple_from_arguments(
        ps: Vec<(Self, Span)>,
    ) -> (Self, Option<Span>) {
        let mut new_p = PatternUnitForRestriction::Const {
            id: TypeId::Intrinsic(IntrinsicType::Unit),
        };
        if let Some(mut span) = ps.get(0).map(|(_, span)| span.clone()) {
            for (p, p_span) in ps.iter().rev() {
                new_p = PatternUnitForRestriction::Tuple(
                    p.clone().into(),
                    new_p.into(),
                );
                span = merge_span(&span, p_span);
            }
            (new_p, Some(span))
        } else {
            (new_p, None)
        }
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
    resolved_variable_map: &FxHashMap<VariableId, Toplevel>,
    candidates_from_implicit_parameters: &FxHashMap<VariableId, Candidate>,
    imports: &mut Imports,
    map: &mut TypeVariableMap,
) -> Result<(Resolved, Vec<Type>, SubtypeRelations), CompileError> {
    // Merge the declarations in a scc to treat them as if they are one declaration,
    let mut resolved_idents = Vec::new();
    let mut name_vec = Vec::new();
    let mut variable_requirements = Vec::new();
    let mut subtype_relations = SubtypeRelations::default();
    let mut pattern_restrictions = PatternRestrictions::default();
    let mut constructors = Vec::new();
    for t in &scc {
        name_vec.push(t.name);
        variable_requirements
            .append(&mut t.type_with_env.variable_requirements.clone());
        subtype_relations.extend(t.type_with_env.subtype_relations.clone());
        constructors.push(SingleTypeConstructor {
            type_: t.type_with_env.constructor.clone(),
            has_annotation: t.type_annotation.is_some(),
        });
        pattern_restrictions
            .extend(t.type_with_env.pattern_restrictions.clone())
    }
    let names_in_scc: FxHashSet<_> = name_vec.iter().copied().collect();
    log::debug!("name of unresolved: {:?}", names_in_scc);
    let mut scc_map: FxHashMap<VariableId, usize> = FxHashMap::default();
    for (i, t) in scc.iter().enumerate() {
        scc_map.insert(t.decl_id, i);
    }
    let candidates_provider = CandidateProvider {
        scc_map: &scc_map,
        f: |j| Candidate {
            type_: if let Some(annotation) = &scc[j].type_annotation {
                annotation.clone().into()
            } else {
                constructors[j].type_.clone().into()
            },
            variable_id: scc[j].decl_id,
        },
        normal_map: resolved_variable_map,
        candidates_from_implicit_parameters,
    };
    // The order of resolving is important.
    // Requirements that are easier to solve should be solved earlier.
    variable_requirements.sort_unstable_by_key(|req| {
        Reverse(difficulty_of_resolving(
            &req.name,
            req.span.start,
            candidates_provider,
        ))
    });
    let mut scc_type = ast_step2::TypeWithEnv {
        constructor: SccTypeConstructor(constructors.clone()),
        variable_requirements,
        subtype_relations,
        pattern_restrictions,
        already_considered_relations: Default::default(),
        fn_apply_dummies: Default::default(),
    };
    resolve_requirements_in_type_with_env(
        scc_type.variable_requirements.len(),
        &mut scc_type,
        candidates_provider,
        map,
        &mut resolved_idents,
        imports,
    )?;
    let variable_requirements = scc_type.variable_requirements;
    let subtype_relation = scc_type.subtype_relations.clone();
    debug_assert!(
        constructors.iter().all(|c| !c.has_annotation)
            || subtype_relation.is_empty()
    );
    Ok((
        resolved_idents,
        scc_type
            .constructor
            .0
            .into_iter()
            .map(|t| {
                let t = simplify::simplify_type(
                    map,
                    ast_step2::TypeWithEnv {
                        constructor: t.type_,
                        variable_requirements: variable_requirements.clone(),
                        subtype_relations: subtype_relation.clone(),
                        pattern_restrictions: scc_type
                            .pattern_restrictions
                            .clone(),
                        already_considered_relations: scc_type
                            .already_considered_relations
                            .clone(),
                        fn_apply_dummies: scc_type.fn_apply_dummies.clone(),
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
                    if !t.subtype_relations.is_empty() {
                        panic!("remaining rels = {}", t.subtype_relations)
                    }
                    debug_assert!(t.variable_requirements.is_empty());
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
        scc_type.subtype_relations,
    ))
}

#[derive(Debug, PartialEq, Eq)]
struct Difficulty {
    multiple_candidates: bool,
    start: usize,
}

fn difficulty_of_resolving<F: FnMut(usize) -> Candidate + Copy>(
    req_name: &[VariableId],
    span_start: usize,
    resolved_variable_map: CandidateProvider<'_, F>,
) -> Difficulty {
    Difficulty {
        multiple_candidates: resolved_variable_map
            .get_candidates(req_name)
            .count()
            > 1,
        start: span_start,
    }
}

impl Ord for Difficulty {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.multiple_candidates, self.start)
            .cmp(&(other.multiple_candidates, other.start))
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
    type_of_improved_decl: T,
    implicit_args: Vec<(Name, Type, IdentId)>,
    map: TypeVariableMap,
    number_of_variable_requirements_added: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    type_: ast_step2::TypeWithEnv,
    variable_id: VariableId,
}

#[derive(Debug, Clone, Copy)]
struct CandidateProvider<'b, F: FnMut(usize) -> Candidate> {
    scc_map: &'b FxHashMap<VariableId, usize>,
    f: F,
    normal_map: &'b FxHashMap<VariableId, Toplevel>,
    candidates_from_implicit_parameters: &'b FxHashMap<VariableId, Candidate>,
}

impl<'b, F: FnMut(usize) -> Candidate + Copy + 'b> CandidateProvider<'b, F> {
    fn get_candidates(
        mut self,
        req_name: &'b [VariableId],
    ) -> impl Iterator<Item = Candidate> + 'b {
        req_name.iter().map(move |n| {
            if let Some(c) = self.normal_map.get(n).cloned().map(|t| {
                let type_ = if let Some(annotation) = t.type_annotation {
                    annotation.into()
                } else {
                    t.type_with_env
                };
                Candidate {
                    type_,
                    variable_id: t.decl_id,
                }
            }) {
                c
            } else if let Some(c) =
                self.candidates_from_implicit_parameters.get(n)
            {
                c.clone()
            } else if let Some(c) = self.scc_map.get(n) {
                (self.f)(*c)
            } else {
                panic!()
            }
        })
    }
}

fn find_satisfied_types<T: TypeConstructor>(
    req: &VariableRequirement,
    type_of_unresolved_decl: &ast_step2::TypeWithEnv<T>,
    resolved_variable_map: CandidateProvider<
        impl FnMut(usize) -> Candidate + Copy,
    >,
    map: &TypeVariableMap,
    resolved_implicit_args: &mut Vec<(IdentId, ResolvedIdent)>,
    imports: &mut Imports,
) -> (
    Vec<SatisfiedType<ast_step2::TypeWithEnv<T>>>,
    Vec<CompileError>,
) {
    log::trace!("type_of_unresolved_decl:");
    log::trace!("{}", type_of_unresolved_decl);
    log::trace!("required_type : {}", req.required_type);
    debug_assert!(!req.name.is_empty());
    let candidates = resolved_variable_map
        .get_candidates(&req.name)
        .collect_vec();
    let is_single_candidate = candidates.len() == 1;
    candidates
        .into_iter()
        .map(
            |Candidate {
                 type_: mut cand_t,
                 variable_id,
             }| {
                let mut t = type_of_unresolved_decl.clone();
                let mut map = map.clone();
                log::debug!("req: {}", req.required_type);
                log::debug!("~~ {:?} : {}", req.name, cand_t);
                let mut implicit_args = Vec::new();
                let type_args;
                (cand_t.constructor, type_args) =
                    cand_t.constructor.remove_parameters();
                cand_t.constructor = match cand_t.constructor.matchable() {
                    TypeMatchable::Restrictions {
                        t: constructor,
                        variable_requirements,
                        subtype_relations,
                    } => {
                        for (interface_v_name_str, interface_v_t) in
                            variable_requirements
                        {
                            let simple_name = Name::from_str(
                                req.module_path,
                                &interface_v_name_str,
                            );
                            let interface_v_name = imports.get_variables(
                                req.module_path,
                                req.module_path,
                                &interface_v_name_str,
                                None,
                                &mut Default::default(),
                                &req.additional_candidates
                                    .iter()
                                    .map(|(a, b)| (a.as_str(), b.clone()))
                                    .collect(),
                            )?;
                            let arg = IdentId::new();
                            implicit_args.push((
                                simple_name,
                                interface_v_t.clone(),
                                arg,
                            ));
                            if let Some((_, decl_id, found_t)) =
                                req.local_env.iter().find(|(name, _, _)| {
                                    interface_v_name_str == *name
                                })
                            {
                                resolved_implicit_args.push((
                                    arg,
                                    ResolvedIdent {
                                        variable_id: VariableId::Local(
                                            *decl_id,
                                        ),
                                        implicit_args: Default::default(),
                                    },
                                ));
                                map.insert_type(
                                    &mut t.subtype_relations,
                                    interface_v_t.clone(),
                                    found_t.clone(),
                                    Some(RelOrigin {
                                        left: interface_v_t,
                                        right: found_t.clone(),
                                        span: req.span.clone(),
                                    }),
                                );
                            } else {
                                cand_t.variable_requirements.push(
                                    VariableRequirement {
                                        name: interface_v_name,
                                        module_path: req.module_path,
                                        required_type: interface_v_t,
                                        ident: arg,
                                        local_env: req.local_env.clone(),
                                        span: req.span.clone(),
                                        additional_candidates: req
                                            .additional_candidates
                                            .clone(),
                                        req_recursion_count: req
                                            .req_recursion_count
                                            + 1,
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
                let mut dummies = BTreeMap::default();
                let constructor_before_replacement = cand_t.constructor.clone();
                cand_t.constructor =
                    replace_fn_apply(cand_t.constructor, &mut dummies);
                for (a, b) in dummies {
                    let i = t.fn_apply_dummies.insert(
                        a,
                        (
                            b,
                            RelOrigin {
                                left: cand_t.constructor.clone(),
                                right: constructor_before_replacement.clone(),
                                span: req.span.clone(),
                            },
                        ),
                    );
                    debug_assert!(i.is_none());
                }
                map.insert_type(
                    &mut t.subtype_relations,
                    cand_t.constructor.clone(),
                    required_type.clone(),
                    Some(RelOrigin {
                        left: cand_t.constructor.clone(),
                        right: required_type,
                        span: req.span.clone(),
                    }),
                );
                t.subtype_relations.extend(cand_t.subtype_relations.clone());
                let implicit_parameters_len =
                    cand_t.variable_requirements.len();
                if is_single_candidate {
                    for req in &cand_t.variable_requirements {
                        let diff = difficulty_of_resolving(
                            &req.name,
                            req.span.start,
                            resolved_variable_map,
                        );
                        let i = t.variable_requirements.partition_point(|r| {
                            difficulty_of_resolving(
                                &r.name,
                                r.span.start,
                                resolved_variable_map,
                            ) > diff
                        });
                        t.variable_requirements.insert(i, req.clone());
                    }
                } else {
                    t.variable_requirements
                        .extend(cand_t.variable_requirements.clone());
                }
                let t = if is_single_candidate {
                    Ok(t)
                } else {
                    simplify::simplify_type(&mut map, t)
                };
                match t {
                    Ok(mut t) => {
                        if req.req_recursion_count
                            == IMPLICIT_PARAMETER_RECURSION_LIMIT
                        {
                            return Err(CompileError::RecursionLimit);
                        }
                        if !is_single_candidate {
                            resolve_requirements_in_type_with_env(
                                implicit_parameters_len,
                                &mut t,
                                resolved_variable_map,
                                &mut map,
                                resolved_implicit_args,
                                imports,
                            )?;
                        }
                        Ok(SatisfiedType {
                            id_of_satisfied_variable: variable_id,
                            type_of_improved_decl: t,
                            implicit_args,
                            type_of_satisfied_variable: cand_t.constructor,
                            map,
                            number_of_variable_requirements_added:
                                if is_single_candidate {
                                    implicit_parameters_len
                                } else {
                                    0
                                },
                        })
                    }
                    Err(r) => Err(r),
                }
            },
        )
        .partition_result()
}

fn replace_fn_apply(t: Type, dummies: &mut BTreeMap<Type, Type>) -> Type {
    use TypeUnit::*;
    fn replace_fn_apply_unit(
        t: TypeUnit,
        dummies: &mut BTreeMap<Type, Type>,
    ) -> Type {
        match t {
            TypeLevelApply { f, a }
                if matches!(
                    f.matchable_ref(),
                    TypeMatchableRef::Variable(TypeVariable::Normal(_))
                ) =>
            {
                let a = replace_fn_apply(a, dummies);
                let t = Type::from(TypeLevelApply { f, a });
                if let Some(t) = dummies.get(&t) {
                    t.clone()
                } else {
                    let new_t: Type = TypeUnit::new_variable().into();
                    dummies.insert(t, new_t.clone());
                    new_t
                }
            }
            Fn(a, b) => {
                Fn(replace_fn_apply(a, dummies), replace_fn_apply(b, dummies))
                    .into()
            }
            RecursiveAlias { body } => RecursiveAlias { body }.into(),
            TypeLevelFn(a) => TypeLevelFn(a).into(),
            TypeLevelApply { f, a } => TypeLevelApply {
                f: replace_fn_apply(f, dummies),
                a: replace_fn_apply(a, dummies),
            }
            .into(),
            Restrictions {
                t,
                variable_requirements,
                subtype_relations,
            } => Restrictions {
                t: replace_fn_apply(t, dummies),
                variable_requirements,
                subtype_relations,
            }
            .into(),
            a @ (Variable(_) | Const { .. }) => a.into(),
            Tuple(a, b) => Tuple(
                replace_fn_apply(a, dummies),
                replace_fn_apply(b, dummies),
            )
            .into(),
        }
    }
    t.into_iter()
        .flat_map(|t| replace_fn_apply_unit(unwrap_or_clone(t), dummies))
        .collect()
}

fn get_one_satisfied<T: Display>(
    satisfied: Vec<SatisfiedType<T>>,
    es: Vec<CompileError>,
    variable_name: Vec<VariableId>,
    span_of_req: Span,
) -> Result<SatisfiedType<T>, CompileError> {
    match satisfied.len() {
        0 => Err(CompileError::NoSuitableVariable {
            name: format!("{variable_name:?}"),
            reason: es,
        }),
        1 => Ok(satisfied.into_iter().next().unwrap()),
        _ => Err(CompileError::ManyCandidates {
            satisfied: satisfied
                .iter()
                .map(|s| {
                    (
                        s.type_of_satisfied_variable.clone(),
                        format!(
                            "{} : {}",
                            s.id_of_satisfied_variable, s.type_of_improved_decl
                        ),
                    )
                })
                .collect(),
            span: span_of_req,
        }),
    }
}

fn resolve_requirements_in_type_with_env(
    mut resolve_num: usize,
    type_of_unresolved_decl: &mut ast_step2::TypeWithEnv<impl TypeConstructor>,
    resolved_variable_map: CandidateProvider<
        impl FnMut(usize) -> Candidate + Copy,
    >,
    map: &mut TypeVariableMap,
    resolved_idents: &mut Vec<(IdentId, ResolvedIdent)>,
    imports: &mut Imports,
) -> Result<(), CompileError> {
    while resolve_num > 0 {
        resolve_num -= 1;
        let req = type_of_unresolved_decl.variable_requirements.pop().unwrap();
        let (satisfied, es) = find_satisfied_types(
            &req,
            type_of_unresolved_decl,
            resolved_variable_map,
            map,
            resolved_idents,
            imports,
        );
        debug_assert_eq!(req.name.len(), satisfied.len() + es.len());
        let satisfied = get_one_satisfied(satisfied, es, req.name, req.span)?;
        resolved_idents.push((
            req.ident,
            ResolvedIdent {
                variable_id: satisfied.id_of_satisfied_variable,
                implicit_args: satisfied.implicit_args,
            },
        ));
        *map = satisfied.map;
        *type_of_unresolved_decl = satisfied.type_of_improved_decl;
        resolve_num += satisfied.number_of_variable_requirements_added;
    }
    *type_of_unresolved_decl =
        simplify::simplify_type(map, type_of_unresolved_decl.clone())?;
    Ok(())
}

fn constructor_type(d: &DataDecl) -> TypeUnit {
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

fn accessor_type(d: &DataDecl, i: usize) -> TypeUnit {
    let fields: Vec<_> = d
        .fields
        .iter()
        .enumerate()
        .map(|(i, _t)| {
            TypeUnit::Variable(TypeVariable::RecursiveIndex(i)).into()
        })
        .rev()
        .collect();
    let t = TypeUnit::Tuple(
        TypeUnit::Const {
            id: TypeId::DeclId(d.decl_id),
        }
        .into(),
        Type::argument_tuple_from_arguments(fields),
    );
    let mut t = TypeUnit::Fn(
        t.into(),
        TypeUnit::Variable(TypeVariable::RecursiveIndex(i)).into(),
    );
    for _ in 0..d.fields.len() {
        t = TypeUnit::TypeLevelFn(t.into())
    }
    t
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableRequirement {
    pub name: Vec<VariableId>,
    pub module_path: Name,
    pub required_type: Type,
    pub ident: IdentId,
    pub span: Span,
    pub local_env: Vec<(String, DeclId, Type)>,
    pub additional_candidates: FxHashMap<String, Vec<DeclId>>,
    pub req_recursion_count: usize,
}
