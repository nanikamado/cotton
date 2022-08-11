mod simplify;

pub use crate::ast_step3::type_check::simplify::TypeVariableTracker;
use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        ident_id::IdentId,
        types,
        types::{Type, TypeUnit, TypeVariable},
        Ast, DataDecl, Expr, ExprWithType, FnArm, Pattern, TypeId,
    },
    intrinsics::IntrinsicVariable,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::{multiunzip, Itertools};
use petgraph::{
    algo::kosaraju_scc, graph::NodeIndex, visit::IntoNodeReferences,
    Graph,
};
use std::{cmp::Reverse, collections::BTreeSet, fmt::Display};
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
    TypeVariableTracker<'a>,
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
    let mut type_variable_tracker = TypeVariableTracker::default();
    for d in &ast.variable_decl {
        let (mut t, resolved, mut ident_type) =
            min_type_incomplite(&d.value, &mut type_variable_tracker);
        resolved_idents.extend(resolved);
        ident_type_map.append(&mut ident_type);
        let type_annotation: Option<ast_step2::IncompleteType> =
            if let Some(annotation) = &d.type_annotation {
                t.subtype_relation.insert((
                    t.constructor.clone(),
                    annotation.constructor.clone(),
                ));
                t.subtype_relation.insert((
                    annotation.constructor.clone(),
                    t.constructor.clone(),
                ));
                t.subtype_relation
                    .extend(annotation.subtype_relation.clone());
                t.variable_requirements.append(
                    &mut annotation.variable_requirements.clone(),
                );
                Some(annotation.clone())
            } else {
                None
            };
        let (incomplete, tracker) =
            simplify::simplify_type(t.into()).unwrap().destruct();
        type_variable_tracker = type_variable_tracker.merge(tracker);
        toplevels.push(Toplevel {
            incomplete,
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
    let (mut resolved_names, types, tracker) =
        resolve_names(toplevels);
    type_variable_tracker = type_variable_tracker.merge(tracker);
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
                        .map(|(v, t)| {
                            (v, type_variable_tracker.find(t))
                        })
                        .collect(),
                ),
            )
        })
        .collect();
    log::debug!("ok");
    (
        resolved_idents,
        types.into_iter().collect(),
        type_variable_tracker,
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
) -> (Resolved, TypesOfDeclsVec, TypeVariableTracker<'a>) {
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
                .flat_map(|(to_name, _, _)| &toplevle_map[to_name])
                .map(move |to| (*to, from))
        })
        .collect_vec();
    for (from, to) in edges {
        toplevel_graph.add_edge(from, to, ());
    }
    let toplevel_sccs = kosaraju_scc(&toplevel_graph);
    let mut resolved_variable_map = FxHashMap::default();
    let mut resolved_idents = Vec::new();
    let mut type_variable_tracker = TypeVariableTracker::default();
    for scc in toplevel_sccs.into_iter().rev() {
        let unresolved_variables = scc
            .into_iter()
            .map(|i| toplevel_graph[i].clone())
            .collect_vec();
        let mut resolved = resolve_scc(
            unresolved_variables.clone(),
            &resolved_variable_map,
        );
        resolved_idents.append(&mut resolved.0);
        type_variable_tracker =
            type_variable_tracker.merge(resolved.2);
        for (toplevel, improved_type) in
            unresolved_variables.into_iter().zip(resolved.1)
        {
            debug_assert_eq!(
                improved_type,
                simplify::simplify_type(improved_type.clone().into())
                    .unwrap()
                    .destruct()
                    .0
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
    (resolved_idents, types, type_variable_tracker)
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SccTypeConstructor<'a>(Vec<Type<'a>>);

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

impl<'a> TypeConstructor<'a> for SccTypeConstructor<'a> {
    fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        self.0
            .iter()
            .flat_map(TypeConstructor::all_type_variables)
            .collect()
    }

    fn replace_num(self, from: TypeVariable, to: &Type<'a>) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_num(from, to))
                .collect(),
        )
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

    fn find_recursive_alias(
        &self,
    ) -> Option<(TypeVariable, Type<'a>)> {
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

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(self, f: F) -> Self {
        Self(self.0.into_iter().map(f).collect())
    }
}

/// Resolves names in strongly connected declarations.
/// Returns the resolved names and improved type of each declaration.
fn resolve_scc<'a>(
    scc: Vec<Toplevel<'a>>,
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
) -> (
    Resolved,
    Vec<ast_step2::IncompleteType<'a, Type<'a>>>,
    TypeVariableTracker<'a>,
) {
    // Merge the declarations in a scc to treate them as if they are one declaration,
    let mut resolved_idents = Vec::new();
    let mut name_vec = Vec::new();
    let mut variable_requirements = Vec::new();
    let mut subtype_relation = BTreeSet::default();
    let mut types = Vec::new();
    for t in &scc {
        name_vec.push(t.name);
        variable_requirements
            .append(&mut t.incomplete.variable_requirements.clone());
        subtype_relation
            .extend(t.incomplete.subtype_relation.clone());
        types.push(t.incomplete.constructor.clone());
    }
    let names_in_scc: FxHashSet<_> =
        name_vec.iter().copied().collect();
    log::debug!("name of unresolved: {:?}", names_in_scc);
    // The order of resolving is important.
    // Requirements that are easier to solve should be solved earlier.
    variable_requirements.sort_unstable_by_key(|(req_name, _, _)| {
        (
            !names_in_scc.contains(req_name),
            resolved_variable_map
                .get(req_name)
                .map(|v| Reverse(v.len())),
        )
    });
    let mut unresolved_type = simplify::IncompleteType {
        constructor: SccTypeConstructor(types),
        variable_requirements,
        type_variable_tracker: TypeVariableTracker {
            map: Default::default(),
            subtype_relation,
        },
    };
    // Recursions are not resolved in this loop.
    while let Some((req_name, req_type, ident_id)) =
        unresolved_type.variable_requirements.pop()
    {
        if names_in_scc.contains(req_name) {
            unresolved_type
                .variable_requirements
                .push((req_name, req_type, ident_id));
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
        );
        let satisfied = get_one_satisfied(satisfied);
        resolved_idents.push((
            ident_id,
            satisfied.id_of_satisfied_variable,
            satisfied.type_args,
        ));
        unresolved_type = satisfied.type_of_improved_decl;
    }
    // Resolve recursive requirements.
    let (mut resolved, improved_types) = resolve_recursion_in_scc(
        unresolved_type,
        &scc,
        resolved_variable_map,
    );
    resolved_idents.append(&mut resolved);
    let variable_requirements = improved_types.variable_requirements;
    let subtype_relation = improved_types
        .type_variable_tracker
        .subtype_relation
        .clone();
    (
        resolved_idents,
        improved_types
            .constructor
            .0
            .into_iter()
            .map(|t| ast_step2::IncompleteType {
                constructor: t,
                variable_requirements: variable_requirements.clone(),
                subtype_relation: subtype_relation.clone(),
            })
            .collect(),
        improved_types.type_variable_tracker,
    )
}

struct SatisfiedType<T> {
    id_of_satisfied_variable: VariableId,
    type_of_improved_decl: T,
    type_args: Vec<(TypeVariable, TypeVariable)>,
}

fn find_satisfied_types<'a, T: TypeConstructor<'a>>(
    type_of_unresolved_decl: &simplify::IncompleteType<'a, T>,
    required_type: &Type<'a>,
    candidates: impl Iterator<Item = Toplevel<'a>>,
    replace_variables: bool,
) -> Vec<SatisfiedType<simplify::IncompleteType<'a, T>>> {
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
            t.type_variable_tracker.add_subtype_rel(
                cand_t.constructor,
                required_type.clone(),
            );
            t.type_variable_tracker
                .add_subtype_rels(cand_t.subtype_relation);
            let decl_id = candidate.decl_id;
            simplify::simplify_type(t).map(|type_of_improved_decl| {
                SatisfiedType {
                    id_of_satisfied_variable: decl_id,
                    type_of_improved_decl,
                    type_args,
                }
            })
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
    mut scc: simplify::IncompleteType<'a, SccTypeConstructor<'a>>,
    toplevels: &[Toplevel<'a>],
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
) -> (
    Resolved,
    simplify::IncompleteType<'a, SccTypeConstructor<'a>>,
) {
    let mut scc_map: FxHashMap<&str, Vec<usize>> =
        FxHashMap::default();
    for (i, t) in toplevels.iter().enumerate() {
        scc_map.entry(t.name).or_default().push(i);
    }
    let mut resolved_idents = Vec::new();
    while let Some((req_name, req_type, ident_id)) =
        scc.variable_requirements.pop()
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
        );
        satisfied.append(&mut find_satisfied_types(
            &scc,
            &req_type,
            scc_map.get(req_name).unwrap().iter().map(|j| Toplevel {
                incomplete: scc.constructor.0[*j].clone().into(),
                ..toplevels[*j].clone()
            }),
            false,
        ));
        let satisfied = get_one_satisfied(satisfied);
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
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> (
    ast_step2::IncompleteType<'a>,
    Resolved,
    Vec<(IdentId, TypeVariable)>,
) {
    match expr {
        Expr::Lambda(arms) => {
            let (
                arm_types,
                variable_requirements,
                subtype_relation,
                resolved_idents,
                ident_type_map,
            ): (Vec<_>, Vec<_>, Vec<_>, Vec<_>, Vec<_>) =
                multiunzip(arms.iter().map(|arm| {
                    arm_min_type(arm, type_variable_tracker)
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
                    let t: Type = arm_types
                        .iter_mut()
                        .flat_map(|arm_type| arm_type.next().unwrap())
                        .collect();
                    t
                })
                .collect();
            let rtn_type: Type = arm_types
                .into_iter()
                .flat_map(types_to_fn_type)
                .collect();
            let constructor: Type = types_to_fn_type(
                arg_types
                    .into_iter()
                    .chain(std::iter::once(rtn_type)),
            );
            type_variable_tracker
                .insert(*type_variable, constructor.clone());
            (
                ast_step2::IncompleteType {
                    constructor,
                    variable_requirements: variable_requirements
                        .concat(),
                    subtype_relation: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                },
                resolved_idents,
                ident_type_map.concat(),
            )
        }
        Expr::Number(_) => {
            let t = Type::from_str("I64");
            type_variable_tracker.insert(*type_variable, t.clone());
            (t.into(), Default::default(), Default::default())
        }
        Expr::StrLiteral(_) => {
            let t = Type::from_str("String");
            type_variable_tracker.insert(*type_variable, t.clone());
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
                    variable_requirements: vec![(info, t, *ident_id)],
                    subtype_relation: BTreeSet::new(),
                },
                Default::default(),
                vec![(*ident_id, *type_variable)],
            )
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1, ident_type_map1) =
                min_type_incomplite(f, type_variable_tracker);
            let (a_t, resolved2, ident_type_map2) =
                min_type_incomplite(a, type_variable_tracker);
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
                    subtype_relation: vec![
                        f_sub_cb,
                        cb_sub_f,
                        a_sub_c,
                        f_t.subtype_relation,
                        a_t.subtype_relation,
                    ]
                    .into_iter()
                    .flatten()
                    .collect(),
                },
                [resolved1, resolved2].concat(),
                [ident_type_map1, ident_type_map2].concat(),
            )
        }
        Expr::Do(es) => {
            let mut variable_requirements = Vec::new();
            let mut subtype_relation = BTreeSet::new();
            let mut resolved_idents = Vec::default();
            let mut ident_type_map = Vec::new();
            let t = es
                .iter()
                .map(|e| {
                    let (t, resolved, mut ident_type) =
                        min_type_incomplite(e, type_variable_tracker);
                    variable_requirements
                        .append(&mut t.variable_requirements.clone());
                    subtype_relation
                        .extend(t.subtype_relation.clone());
                    resolved_idents.extend(resolved);
                    ident_type_map.append(&mut ident_type);
                    t
                })
                .collect::<Vec<_>>();
            let t = t.last().unwrap().clone();
            type_variable_tracker
                .insert(*type_variable, t.constructor.clone());
            (
                ast_step2::IncompleteType {
                    constructor: t.constructor,
                    variable_requirements,
                    subtype_relation,
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

type VariableRequirement<'a> = (&'a str, types::Type<'a>, IdentId);
type SubtypeRelation<'a> =
    BTreeSet<(types::Type<'a>, types::Type<'a>)>;
type IdentTypeMap = Vec<(IdentId, TypeVariable)>;

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type<'a>(
    arm: &FnArm<'a>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> (
    Vec<types::Type<'a>>,
    Vec<VariableRequirement<'a>>,
    SubtypeRelation<'a>,
    Resolved,
    IdentTypeMap,
) {
    let (body_type, mut resolved_idents, ident_type_map) =
        min_type_incomplite(&arm.expr, type_variable_tracker);
    let (mut ts, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).unzip();
    ts.push(body_type.constructor);
    let bindings: FxHashMap<&str, (DeclId, types::Type)> = bindings
        .into_iter()
        .flatten()
        .map(|(n, i, t)| (n, (i, t)))
        .collect();
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
        variable_requirements,
        {
            let mut tmp = body_type.subtype_relation;
            tmp.append(
                &mut subtype_requirement.into_iter().collect(),
            );
            tmp
        },
        resolved_idents,
        ident_type_map,
    )
}

fn pattern_to_type<'a>(
    p: &Pattern<'a>,
) -> (types::Type<'a>, Vec<(&'a str, DeclId, types::Type<'a>)>) {
    match p {
        Pattern::Number(_) => (Type::from_str("I64"), Vec::new()),
        Pattern::StrLiteral(_) => {
            (Type::from_str("String"), Vec::new())
        }
        Pattern::Constructor { id, args } => {
            let (types, bindings): (Vec<_>, Vec<_>) =
                args.iter().map(pattern_to_type).unzip();
            (
                TypeUnit::Normal {
                    name: id.name(),
                    args: types,
                    id: (*id).into(),
                }
                .into(),
                bindings.concat(),
            )
        }
        Pattern::Binder(name, decl_id) => {
            let t: types::Type = TypeUnit::new_variable().into();
            (t.clone(), vec![(name, *decl_id, t)])
        }
        Pattern::Underscore => {
            (TypeUnit::new_variable().into(), Vec::new())
        }
    }
}
