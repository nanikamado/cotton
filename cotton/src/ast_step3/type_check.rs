mod simplify;

pub use self::simplify::TypeVariableMap;
use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        ident_id::IdentId,
        types::{self, SingleTypeConstructor, TypeMatchable},
        types::{Type, TypeUnit, TypeVariable},
        Ast, DataDecl, Expr, ExprWithType, FnArm, IncompleteType,
        Pattern, PatternRestrictions, PatternUnit,
        PatternUnitForRestriction, SubtypeRelations, TypeId,
    },
    intrinsics::{IntrinsicType, IntrinsicVariable},
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::{multiunzip, Itertools};
use petgraph::{
    algo::kosaraju_scc, graph::NodeIndex, visit::IntoNodeReferences,
    Graph,
};
use std::{cmp::Reverse, fmt::Display};
use strum::IntoEnumIterator;
use types::TypeConstructor;

#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum VariableId {
    Decl(DeclId),
    Intrinsic(IntrinsicVariable),
}

impl Display for VariableId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => a.fmt(f),
            VariableId::Intrinsic(a) => a.fmt(f),
        }
    }
}

impl std::fmt::Debug for VariableId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => write!(f, "VariableId({})", a),
            VariableId::Intrinsic(a) => {
                write!(f, "VariableId({})", a)
            }
        }
    }
}

pub type ResolvedIdents<'a> =
    FxHashMap<IdentId, (VariableId, Vec<(TypeVariable, Type<'a>)>)>;

pub fn type_check<'a>(
    ast: &Ast<'a>,
) -> (
    ResolvedIdents<'a>,
    FxHashMap<DeclId, ast_step2::IncompleteType<'a>>,
    SubtypeRelations<'a>,
    TypeVariableMap<'a>,
) {
    let mut toplevels: Vec<Toplevel<'a>> = Default::default();
    for v in IntrinsicVariable::iter() {
        toplevels.push(Toplevel {
            incomplete: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Intrinsic(v),
            name: v.to_str(),
        });
    }
    for d in &ast.data_decl {
        let d_type: types::Type = constructor_type(d.clone()).into();
        toplevels.push(Toplevel {
            incomplete: d_type.into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
        });
    }
    let mut resolved_idents = Vec::new();
    let mut ident_type_map = Vec::new();
    let mut subtype_relations = SubtypeRelations::default();
    let mut map = TypeVariableMap::default();
    for d in &ast.variable_decl {
        let (mut t, resolved, mut ident_type) = min_type_incomplite(
            &d.value,
            &mut subtype_relations,
            &mut map,
        );
        resolved_idents.extend(resolved);
        ident_type_map.append(&mut ident_type);
        let type_annotation: Option<ast_step2::IncompleteType> =
            if let Some(annotation) = &d.type_annotation {
                t.subtype_relations.insert((
                    t.constructor.clone(),
                    annotation.constructor.clone(),
                ));
                t.subtype_relations
                    .extend(annotation.subtype_relations.clone());
                t.variable_requirements.append(
                    &mut annotation.variable_requirements.clone(),
                );
                Some(annotation.clone())
            } else {
                None
            };
        let incomplete = simplify::simplify_type(
            &mut map,
            IncompleteType {
                constructor: SingleTypeConstructor {
                    type_: t.constructor,
                    contravariant_candidates_from_annotation:
                        type_annotation.as_ref().map(|t| {
                            t.constructor
                                .contravariant_type_variables()
                        }),
                },
                variable_requirements: t.variable_requirements,
                subtype_relations: t.subtype_relations,
                pattern_restrictions: t.pattern_restrictions,
                already_considered_relations: t
                    .already_considered_relations,
            },
        )
        .unwrap();
        subtype_relations = subtype_relations
            .merge(incomplete.subtype_relations.clone());
        toplevels.push(Toplevel {
            incomplete: incomplete.into(),
            type_annotation,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
        });
    }
    for top in &toplevels {
        log::debug!("{:<3} {} : ", top.decl_id, top.name);
        log::debug!("resolved: {:?}", top.resolved_idents);
        if let Some(f) = &top.type_annotation {
            log::debug!("face: {}", f);
            log::debug!("incomplete: {}", top.incomplete);
        } else {
            log::debug!("not face: {}", top.incomplete);
        }
    }
    let (mut resolved_names, types, rel) =
        resolve_names(toplevels, &mut map);
    subtype_relations = subtype_relations.merge(rel);
    for (ident_id, variable_id, _) in
        resolved_names.iter().sorted_unstable()
    {
        log::debug!("{ident_id} => {variable_id:?}");
    }
    resolved_idents.append(&mut resolved_names);
    let resolved_idents = resolved_idents
        .into_iter()
        .map(|(ident_id, variable_id, type_args)| {
            (
                ident_id,
                (
                    variable_id,
                    type_args
                        .into_iter()
                        .map(|(v, t)| (v, map.find(t)))
                        .collect(),
                ),
            )
        })
        .collect();
    log::debug!("ok");
    (
        resolved_idents,
        types.into_iter().collect(),
        subtype_relations,
        map,
    )
}

pub type Resolved =
    Vec<(IdentId, VariableId, Vec<(TypeVariable, TypeVariable)>)>;

#[derive(Debug, Clone)]
struct Toplevel<'a> {
    incomplete: ast_step2::IncompleteType<'a>,
    type_annotation: Option<ast_step2::IncompleteType<'a>>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: &'a str,
}

type TypesOfDeclsVec<'a> =
    Vec<(DeclId, ast_step2::IncompleteType<'a>)>;

fn resolve_names<'a>(
    toplevels: Vec<Toplevel<'a>>,
    map: &mut TypeVariableMap<'a>,
) -> (Resolved, TypesOfDeclsVec<'a>, SubtypeRelations<'a>) {
    let mut toplevel_graph = Graph::<Toplevel, ()>::new();
    for t in toplevels {
        toplevel_graph.add_node(t);
    }
    let mut toplevle_map: FxHashMap<&str, Vec<NodeIndex>> =
        FxHashMap::default();
    for (i, t) in toplevel_graph.node_references() {
        toplevle_map.entry(t.name).or_default().push(i);
    }
    let edges = toplevel_graph
        .node_references()
        .flat_map(|(from, from_toplevle)| {
            from_toplevle
                .incomplete
                .variable_requirements
                .iter()
                .flat_map(|(to_name, _, _, _)| &toplevle_map[to_name])
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
        );
        resolved_idents.append(&mut resolved.0);
        rel = rel.merge(resolved.2);
        for (toplevel, improved_type) in
            unresolved_variables.into_iter().zip(resolved.1)
        {
            debug_assert_eq!(
                improved_type,
                simplify::simplify_type(map, improved_type.clone())
                    .unwrap()
            );
            log::debug!(
                "improved type of {}:\n{}",
                toplevel.name,
                improved_type
            );
            resolved_variable_map
                .entry(toplevel.name)
                .or_default()
                .push(Toplevel {
                    incomplete: improved_type,
                    ..toplevel
                });
        }
    }
    let mut types = Vec::new();
    for (i, t) in resolved_variable_map.into_iter().flat_map(
        |(_, toplevels)| {
            toplevels.into_iter().map(|t| (t.decl_id, t.incomplete))
        },
    ) {
        match i {
            VariableId::Decl(i) => {
                types.push((i, t));
            }
            VariableId::Intrinsic(_) => (),
        }
    }
    (resolved_idents, types, rel)
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SccTypeConstructor<'a>(Vec<SingleTypeConstructor<'a>>);

impl Display for SccTypeConstructor<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.0.iter().join(", "))?;
        write!(f, "]")
    }
}

impl<'a> Type<'a> {
    fn argument_tuple_from_arguments(ts: Vec<Self>) -> Self {
        let mut new_ts = Type::from_str("()");
        for t in ts.into_iter().rev() {
            new_ts = TypeUnit::Normal {
                name: "AT",
                args: vec![t, new_ts],
                id: TypeId::Intrinsic(IntrinsicType::ArgumentTuple),
            }
            .into();
        }
        new_ts
    }

    fn arguments_from_argument_tuple(self) -> Vec<Self> {
        use TypeMatchable::*;
        match self.matchable() {
            Normal { args, id, .. }
                if id
                    == TypeId::Intrinsic(
                        IntrinsicType::ArgumentTuple,
                    ) =>
            {
                let mut args = args.into_iter();
                std::iter::once(args.next().unwrap())
                    .chain(
                        args.next()
                            .unwrap()
                            .arguments_from_argument_tuple(),
                    )
                    .collect()
            }
            Normal { id, .. }
                if id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            t => {
                panic!(
                    "expected AT or Unit but got {}",
                    Type::from(t)
                )
            }
        }
    }
}

impl<'a> PatternUnitForRestriction<'a> {
    fn argument_tuple_from_arguments(
        pss: Vec<Vec<Self>>,
    ) -> Vec<Self> {
        let mut new_pattern = Vec::new();
        for ps in pss {
            let mut new_p = PatternUnitForRestriction::Constructor {
                id: TypeId::Intrinsic(IntrinsicType::Unit),
                name: "()",
                args: Vec::new(),
            };
            for p in ps.iter().rev() {
                new_p = PatternUnitForRestriction::Constructor {
                    id: TypeId::Intrinsic(
                        IntrinsicType::ArgumentTuple,
                    ),
                    name: "AT",
                    args: vec![p.clone(), new_p],
                };
            }
            new_pattern.push(new_p);
        }
        new_pattern
    }

    fn arguments_from_argument_tuple(self) -> Vec<Self> {
        use PatternUnitForRestriction::*;
        match self {
            Constructor { args, id, .. }
                if id
                    == TypeId::Intrinsic(
                        IntrinsicType::ArgumentTuple,
                    ) =>
            {
                let mut args = args.into_iter();
                std::iter::once(args.next().unwrap())
                    .chain(
                        args.next()
                            .unwrap()
                            .arguments_from_argument_tuple(),
                    )
                    .collect()
            }
            Constructor { id, .. }
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
            Constructor { args, id, .. }
                if *id
                    == TypeId::Intrinsic(
                        IntrinsicType::ArgumentTuple,
                    ) =>
            {
                let mut args = args.iter();
                std::iter::once(args.next().unwrap())
                    .chain(
                        args.next()
                            .unwrap()
                            .arguments_from_argument_tuple_ref(),
                    )
                    .collect()
            }
            Constructor { id, .. }
                if *id == TypeId::Intrinsic(IntrinsicType::Unit) =>
            {
                Vec::new()
            }
            _ => panic!(),
        }
    }
}

impl<'a> TypeConstructor<'a> for SccTypeConstructor<'a> {
    fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        self.all_type_variables_vec().into_iter().collect()
    }

    fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        self.0
            .iter()
            .flat_map(TypeConstructor::all_type_variables_vec)
            .collect()
    }

    fn replace_num(self, from: TypeVariable, to: &Type<'a>) -> Self {
        self.replace_num_with_update_flag(from, to).0
    }

    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type<'a>,
    ) -> (Self, bool) {
        let mut updated = false;
        let t = self.map_type(|t| {
            let (t, u) = t.replace_num_with_update_flag(from, to);
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

    fn find_recursive_alias(&self) -> Option<Type<'a>> {
        self.0
            .iter()
            .find_map(TypeConstructor::find_recursive_alias)
    }

    fn replace_type(
        self,
        from: &TypeUnit<'a>,
        to: &TypeUnit<'a>,
    ) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_type(from, to))
                .collect(),
        )
    }

    fn replace_type_union(
        self,
        from: &Type,
        to: &TypeUnit<'a>,
    ) -> Self {
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
        to: &TypeUnit<'a>,
    ) -> (Self, bool) {
        let mut updated = false;
        let t = self.map_type(|t| {
            let (t, u) =
                t.replace_type_union_with_update_flag(from, to);
            updated = u;
            t
        });
        (t, updated)
    }

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(
        self,
        mut f: F,
    ) -> Self {
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

    fn normalize_contravariant_candidates_from_annotation(
        self,
        map: &mut TypeVariableMap<'a>,
    ) -> Self {
        Self(self.0
            .into_iter()
            .map(|s| {
                s.normalize_contravariant_candidates_from_annotation(
                    map,
                )
            })
            .collect())
    }

    fn contains_variable(&self, v: TypeVariable) -> bool {
        self.0.iter().any(|s| s.contains_variable(v))
    }
}

/// Resolves names in strongly connected declarations.
/// Returns the resolved names and improved type of each declaration.
fn resolve_scc<'a>(
    scc: Vec<Toplevel<'a>>,
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
    map: &mut TypeVariableMap<'a>,
) -> (
    Resolved,
    Vec<ast_step2::IncompleteType<'a, Type<'a>>>,
    SubtypeRelations<'a>,
) {
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
            .append(&mut t.incomplete.variable_requirements.clone());
        subtype_relations
            .extend(t.incomplete.subtype_relations.clone());
        types.push(SingleTypeConstructor {
            type_: t.incomplete.constructor.clone(),
            contravariant_candidates_from_annotation: t
                .type_annotation
                .as_ref()
                .map(|t| {
                    t.constructor.contravariant_type_variables()
                }),
        });
        pattern_restrictions
            .extend(t.incomplete.pattern_restrictions.clone())
    }
    let names_in_scc: FxHashSet<_> =
        name_vec.iter().copied().collect();
    log::debug!("name of unresolved: {:?}", names_in_scc);
    // The order of resolving is important.
    // Requirements that are easier to solve should be solved earlier.
    variable_requirements.sort_unstable_by_key(
        |(req_name, _, _, _)| {
            (
                !names_in_scc.contains(req_name),
                resolved_variable_map
                    .get(req_name)
                    .map(|v| Reverse(v.len())),
            )
        },
    );
    let mut unresolved_type = IncompleteType {
        constructor: SccTypeConstructor(types),
        variable_requirements,
        subtype_relations,
        pattern_restrictions,
        already_considered_relations: Default::default(),
    };
    // Recursions are not resolved in this loop.
    while let Some((
        req_name,
        req_type,
        ident_id,
        ident_type_variable,
    )) = unresolved_type.variable_requirements.pop()
    {
        if names_in_scc.contains(req_name) {
            unresolved_type.variable_requirements.push((
                req_name,
                req_type,
                ident_id,
                ident_type_variable,
            ));
            // Skipping the resolveing of recursion.
            break;
        }
        let satisfied = find_satisfied_types(
            &unresolved_type,
            &req_type,
            resolved_variable_map
                .get(req_name)
                .unwrap_or_else(|| panic!("req_name: {}", req_name))
                .clone()
                .into_iter(),
            true,
            map,
        );
        let satisfied = get_one_satisfied(satisfied);
        resolved_idents.push((
            ident_id,
            satisfied.id_of_satisfied_variable,
            satisfied.type_args.clone(),
        ));
        *map = satisfied.map;
        unresolved_type = satisfied.type_of_improved_decl;
        map.insert(
            &mut unresolved_type.subtype_relations,
            ident_type_variable,
            satisfied.type_of_satisfied_variable,
        );
    }
    // Resolve recursive requirements.
    let (mut resolved, improved_types) = resolve_recursion_in_scc(
        unresolved_type,
        &scc,
        resolved_variable_map,
        map,
    );
    resolved_idents.append(&mut resolved);
    let variable_requirements = improved_types.variable_requirements;
    let subtype_relation = improved_types.subtype_relations.clone();
    (
        resolved_idents,
        improved_types
            .constructor
            .0
            .into_iter()
            .map(|t| {
                simplify::simplify_type(
                    map,
                    ast_step2::IncompleteType {
                        constructor: t.type_,
                        variable_requirements: variable_requirements
                            .clone(),
                        subtype_relations: subtype_relation.clone(),
                        pattern_restrictions: improved_types
                            .pattern_restrictions
                            .clone(),
                        already_considered_relations: improved_types
                            .already_considered_relations
                            .clone(),
                    },
                )
                .unwrap()
            })
            .collect(),
        improved_types.subtype_relations,
    )
}

struct SatisfiedType<'a, T> {
    type_of_satisfied_variable: Type<'a>,
    id_of_satisfied_variable: VariableId,
    type_of_improved_decl: T,
    type_args: Vec<(TypeVariable, TypeVariable)>,
    map: TypeVariableMap<'a>,
}

fn find_satisfied_types<'a, T: TypeConstructor<'a>>(
    type_of_unresolved_decl: &IncompleteType<'a, T>,
    required_type: &Type<'a>,
    candidates: impl Iterator<Item = Toplevel<'a>>,
    replace_variables: bool,
    map: &TypeVariableMap<'a>,
) -> Vec<SatisfiedType<'a, IncompleteType<'a, T>>> {
    log::trace!("type_of_unresolved_decl:");
    log::trace!("{}", type_of_unresolved_decl);
    log::trace!("required_type : {required_type}");
    candidates
        .filter_map(|candidate| {
            let mut t = type_of_unresolved_decl.clone();
            let mut cand_t =
                if let Some(face) = candidate.type_annotation {
                    face
                } else {
                    candidate.incomplete
                };
            let mut type_args = Vec::new();
            log::debug!("~~ {} : {}", candidate.name, cand_t);
            if replace_variables {
                (cand_t, type_args) = cand_t.change_variable_num();
            }
            let mut map = map.clone();
            t.subtype_relations.add_subtype_rel(
                cand_t.constructor.clone(),
                required_type.clone(),
            );
            t.subtype_relations.add_subtype_rel(
                required_type.clone(),
                cand_t.constructor.clone(),
            );
            t.subtype_relations
                .add_subtype_rels(cand_t.subtype_relations);
            let decl_id = candidate.decl_id;
            simplify::simplify_type(&mut map, t).map(
                |type_of_improved_decl| SatisfiedType {
                    id_of_satisfied_variable: decl_id,
                    type_of_improved_decl,
                    type_args,
                    type_of_satisfied_variable: cand_t.constructor,
                    map,
                },
            )
        })
        .collect_vec()
}

fn get_one_satisfied<T: Display>(
    satisfied: Vec<SatisfiedType<T>>,
) -> SatisfiedType<T> {
    match satisfied.len() {
        0 => panic!("name resolve failed"),
        1 => satisfied.into_iter().next().unwrap(),
        _ => {
            panic!(
                "satisfied:\n{}",
                satisfied
                    .iter()
                    .map(|s| format!(
                        "{} : {}",
                        s.id_of_satisfied_variable,
                        s.type_of_improved_decl
                    ))
                    .join("\n")
            )
        }
    }
}

/// The reterned `IncompleteType` does not contain variable_requirements, but contains subtype relationship.
fn resolve_recursion_in_scc<'a>(
    mut scc: IncompleteType<'a, SccTypeConstructor<'a>>,
    toplevels: &[Toplevel<'a>],
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
    map: &mut TypeVariableMap<'a>,
) -> (Resolved, IncompleteType<'a, SccTypeConstructor<'a>>) {
    let mut scc_map: FxHashMap<&str, Vec<usize>> =
        FxHashMap::default();
    for (i, t) in toplevels.iter().enumerate() {
        scc_map.entry(t.name).or_default().push(i);
    }
    let mut resolved_idents = Vec::new();
    while let Some((
        req_name,
        req_type,
        ident_id,
        ident_type_variable,
    )) = scc.variable_requirements.pop()
    {
        let mut satisfied = find_satisfied_types(
            &scc,
            &req_type,
            resolved_variable_map
                .get(req_name)
                .into_iter()
                .flatten()
                .cloned(),
            true,
            map,
        );
        satisfied.append(&mut find_satisfied_types(
            &scc,
            &req_type,
            scc_map.get(req_name).unwrap().iter().map(|j| Toplevel {
                incomplete: scc.constructor.0[*j]
                    .type_
                    .clone()
                    .into(),
                ..toplevels[*j].clone()
            }),
            false,
            map,
        ));
        let satisfied = get_one_satisfied(satisfied);
        *map = satisfied.map;
        map.insert(
            &mut scc.subtype_relations,
            ident_type_variable,
            satisfied.type_of_satisfied_variable,
        );
        resolved_idents.push((
            ident_id,
            satisfied.id_of_satisfied_variable,
            satisfied.type_args,
        ));
        scc = satisfied.type_of_improved_decl;
    }
    (resolved_idents, scc)
}

fn constructor_type(d: DataDecl) -> TypeUnit {
    let fields: Vec<_> = d
        .fields
        .iter()
        .map(|t| TypeUnit::Variable(*t).into())
        .collect();
    let mut t = TypeUnit::Normal {
        name: d.name,
        args: fields.clone(),
        id: TypeId::DeclId(d.decl_id),
    };
    for field in fields.into_iter().rev() {
        t = TypeUnit::Fn(field, t.into())
    }
    t
}

fn min_type_incomplite<'a>(
    (expr, type_variable): &ExprWithType<'a>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> (
    ast_step2::IncompleteType<'a>,
    Resolved,
    Vec<(IdentId, TypeVariable)>,
) {
    match expr {
        Expr::Lambda(arms) => {
            let (
                arm_types,
                restrictions,
                variable_requirements,
                subtype_relation,
                resolved_idents,
                ident_type_map,
                pattern_restrictions,
            ): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = multiunzip(arms.iter().map(|arm| {
                arm_min_type(arm, subtype_relations, map)
            }));
            let resolved_idents = resolved_idents.concat();
            let arg_len =
                arm_types.iter().map(Vec::len).min().unwrap() - 1;
            let mut arm_types = arm_types
                .into_iter()
                .map(Vec::into_iter)
                .collect_vec();
            #[allow(clippy::needless_collect)]
            let arg_types: Vec<Type> = (0..arg_len)
                .map(|_| {
                    let _t: Type = arm_types
                        .iter_mut()
                        .flat_map(|arm_type| arm_type.next().unwrap())
                        .collect();
                    TypeUnit::new_variable().into()
                })
                .collect();
            let rtn_type: Type = arm_types
                .into_iter()
                .flat_map(types_to_fn_type)
                .collect();
            let constructor: Type = types_to_fn_type(
                arg_types
                    .clone()
                    .into_iter()
                    .chain(std::iter::once(rtn_type)),
            );
            let mut pattern_restrictions =
                pattern_restrictions.concat();
            pattern_restrictions.push((
                Type::argument_tuple_from_arguments(arg_types),
                PatternUnitForRestriction::argument_tuple_from_arguments(restrictions),
            ));
            map.insert(
                subtype_relations,
                *type_variable,
                constructor.clone(),
            );
            (
                ast_step2::IncompleteType {
                    constructor,
                    variable_requirements: variable_requirements
                        .concat(),
                    subtype_relations: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                },
                resolved_idents,
                ident_type_map.concat(),
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
        Expr::Ident {
            name: info,
            ident_id,
            ..
        } => {
            let t: Type = TypeUnit::Variable(*type_variable).into();
            (
                ast_step2::IncompleteType {
                    constructor: t.clone(),
                    variable_requirements: vec![(
                        info,
                        t,
                        *ident_id,
                        *type_variable,
                    )],
                    subtype_relations: SubtypeRelations::default(),
                    pattern_restrictions:
                        PatternRestrictions::default(),
                    already_considered_relations: Default::default(),
                },
                Default::default(),
                vec![(*ident_id, *type_variable)],
            )
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1, ident_type_map1) =
                min_type_incomplite(f, subtype_relations, map);
            let (a_t, resolved2, ident_type_map2) =
                min_type_incomplite(a, subtype_relations, map);
            let b: types::Type =
                TypeUnit::Variable(*type_variable).into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn: Type =
                TypeUnit::Fn(c.clone(), b.clone()).into();
            // f < c -> b
            let f_sub_cb = [(f_t.constructor.clone(), cb_fn.clone())]
                .iter()
                .cloned()
                .collect();
            // c -> b < f
            let cb_sub_f =
                [(cb_fn, f_t.constructor)].iter().cloned().collect();
            // a < c
            let a_sub_c =
                [(a_t.constructor, c)].iter().cloned().collect();
            (
                ast_step2::IncompleteType {
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
                },
                [resolved1, resolved2].concat(),
                [ident_type_map1, ident_type_map2].concat(),
            )
        }
        Expr::Do(es) => {
            let mut variable_requirements = Vec::new();
            let mut subtype_relations = SubtypeRelations::default();
            let mut resolved_idents = Vec::default();
            let mut ident_type_map = Vec::new();
            let mut pattern_restrictions =
                PatternRestrictions::default();
            let t = es
                .iter()
                .map(|e| {
                    let (t, resolved, mut ident_type) =
                        min_type_incomplite(
                            e,
                            &mut subtype_relations,
                            map,
                        );
                    variable_requirements
                        .append(&mut t.variable_requirements.clone());
                    subtype_relations
                        .extend(t.subtype_relations.clone());
                    pattern_restrictions
                        .extend(t.pattern_restrictions.clone());
                    resolved_idents.extend(resolved);
                    ident_type_map.append(&mut ident_type);
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
                ast_step2::IncompleteType {
                    constructor: t.constructor,
                    variable_requirements,
                    subtype_relations,
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                },
                resolved_idents,
                ident_type_map,
            )
        }
    }
}

fn types_to_fn_type<'a>(
    types: impl DoubleEndedIterator<Item = Type<'a>>,
) -> Type<'a> {
    let mut ts = types.rev();
    let mut r = ts.next().unwrap();
    for t in ts {
        r = TypeUnit::Fn(t, r).into()
    }
    r
}

type VariableRequirement<'a> =
    (&'a str, types::Type<'a>, IdentId, TypeVariable);
type IdentTypeMap = Vec<(IdentId, TypeVariable)>;

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type<'a>(
    arm: &FnArm<'a>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> (
    Vec<types::Type<'a>>,
    Vec<PatternUnitForRestriction<'a>>,
    Vec<VariableRequirement<'a>>,
    SubtypeRelations<'a>,
    Resolved,
    IdentTypeMap,
    PatternRestrictions<'a>,
) {
    let (body_type, mut resolved_idents, ident_type_map) =
        min_type_incomplite(&arm.expr, subtype_relations, map);
    let (mut ts, bindings, patterns): (Vec<_>, Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).multiunzip();
    ts.push(body_type.constructor);
    let bindings: FxHashMap<&str, (DeclId, types::Type)> =
        bindings.into_iter().flatten().collect();
    let mut variable_requirements = Vec::new();
    let mut subtype_requirement = Vec::new();
    for p in body_type.variable_requirements.into_iter() {
        if let Some(a) = bindings.get(&p.0) {
            subtype_requirement.push((a.1.clone(), p.1.clone()));
            subtype_requirement.push((p.1, a.1.clone()));
            resolved_idents.push((
                p.2,
                VariableId::Decl(a.0),
                Vec::new(),
            ));
        } else {
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
        ident_type_map,
        body_type.pattern_restrictions,
    )
}

fn pattern_unit_to_type<'a>(
    p: &PatternUnit<'a>,
) -> (
    types::Type<'a>,
    FxHashMap<&'a str, (DeclId, types::Type<'a>)>,
    PatternUnitForRestriction<'a>,
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
        Constructor { id, args } => {
            let (types, bindings, pattern_restrictions): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = args.iter().map(pattern_to_type).multiunzip();
            (
                TypeUnit::Normal {
                    name: id.name(),
                    args: types,
                    id: (*id).into(),
                }
                .into(),
                // TypeUnit::new_variable().into(),
                bindings.into_iter().flatten().collect(),
                PatternUnitForRestriction::Constructor {
                    id: (*id).into(),
                    name: id.name(),
                    args: pattern_restrictions,
                },
            )
        }
        Binder(name, decl_id) => {
            let v = TypeVariable::new();
            let t: types::Type = TypeUnit::Variable(v).into();
            (
                t.clone(),
                vec![(*name, (*decl_id, t))].into_iter().collect(),
                PatternUnitForRestriction::Binder(
                    TypeUnit::Variable(v).into(),
                    *decl_id,
                ),
            )
        }
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

fn pattern_to_type<'a>(
    p: &Pattern<'a>,
) -> (
    types::Type<'a>,
    FxHashMap<&'a str, (DeclId, types::Type<'a>)>,
    PatternUnitForRestriction<'a>,
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
