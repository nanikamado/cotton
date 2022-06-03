mod simplify;

use super::type_util::construct_type;
use crate::{
    ast2::{
        decl_id::DeclId,
        ident_id::IdentId,
        types,
        types::{Type, TypeUnit, TypeVariable},
        Ast, DataDecl, Expr, FnArm, IncompleteType, Pattern, TypeId,
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

type Resolved = Vec<(IdentId, VariableId)>;

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

pub fn type_check<'a>(
    ast: &Ast<'a>,
) -> (
    FxHashMap<IdentId, VariableId>,
    FxHashMap<DeclId, IncompleteType<'a>>,
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
        let d_type: types::Type = constructor_type(*d).into();
        toplevels.push(Toplevel {
            incomplete: d_type.into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
        });
    }
    let mut resolved_idents = FxHashMap::default();
    for d in &ast.variable_decl {
        let (mut t, resolved) = min_type(&d.value).unwrap();
        resolved_idents.extend(resolved);
        let type_annotation = if let Some(annotation) =
            &d.type_annotation
        {
            let annotation = annotation.clone().change_variable_num();
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
            Some(annotation)
        } else {
            None
        };
        toplevels.push(Toplevel {
            incomplete: simplify::simplify_type(t).unwrap(),
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
    let (resolved_names, types) = resolve_names(toplevels);
    for (ident_id, variable_id) in
        resolved_names.iter().sorted_unstable()
    {
        log::debug!("{ident_id} => {variable_id}");
    }
    resolved_idents.extend(resolved_names);
    (resolved_idents, types.into_iter().collect())
}

#[derive(Debug, Clone)]
struct Toplevel<'a> {
    incomplete: IncompleteType<'a>,
    type_annotation: Option<IncompleteType<'a>>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: &'a str,
}

type TypesOfDecls<'a> = Vec<(DeclId, IncompleteType<'a>)>;

fn resolve_names(
    toplevels: Vec<Toplevel>,
) -> (Vec<(IdentId, VariableId)>, TypesOfDecls) {
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
        for (toplevel, improved_type) in
            unresolved_variables.into_iter().zip(resolved.1)
        {
            debug_assert_eq!(
                improved_type,
                simplify::simplify_type(improved_type.clone())
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
    let types = resolved_variable_map
        .into_iter()
        .flat_map(|(_, toplevels)| {
            toplevels.into_iter().map(|t| (t.decl_id, t.incomplete))
        })
        .filter_map(|(i, t)| match i {
            VariableId::Decl(i) => Some((i, t)),
            VariableId::Intrinsic(_) => None,
        })
        .collect();
    (resolved_idents, types)
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
}

/// Resolves names in strongly connected declarations.
/// Returns the resolved names and improved type of each declaration.
fn resolve_scc<'a>(
    scc: Vec<Toplevel<'a>>,
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
) -> (
    Vec<(IdentId, VariableId)>,
    Vec<IncompleteType<'a, Type<'a>>>,
    // IncompleteType<'a, SccTypeConstructor<'a>>,
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
    let mut unresolved_type = IncompleteType {
        constructor: SccTypeConstructor(types),
        variable_requirements,
        subtype_relation,
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
        resolved_idents
            .push((ident_id, satisfied.id_of_satisfied_variable));
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
    let subtype_relation = improved_types.subtype_relation;
    (
        resolved_idents,
        improved_types
            .constructor
            .0
            .into_iter()
            .map(|t| IncompleteType {
                constructor: t,
                variable_requirements: variable_requirements.clone(),
                subtype_relation: subtype_relation.clone(),
            })
            .collect(),
    )
}

struct SatisfiedType<T> {
    id_of_satisfied_variable: VariableId,
    type_of_improved_decl: T,
}

fn find_satisfied_types<'a, T: TypeConstructor<'a>>(
    type_of_unresolved_decl: &IncompleteType<'a, T>,
    required_type: &Type<'a>,
    candidates: impl Iterator<Item = Toplevel<'a>>,
    replace_variables: bool,
) -> Vec<SatisfiedType<IncompleteType<'a, T>>> {
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
            if replace_variables {
                cand_t = cand_t.change_variable_num();
            }
            t.subtype_relation
                .insert((cand_t.constructor, required_type.clone()));
            t.subtype_relation.extend(cand_t.subtype_relation);
            let decl_id = candidate.decl_id;
            simplify::simplify_type(t).map(|type_of_improved_decl| {
                SatisfiedType {
                    id_of_satisfied_variable: decl_id,
                    type_of_improved_decl,
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
    mut scc: IncompleteType<'a, SccTypeConstructor<'a>>,
    toplevels: &[Toplevel<'a>],
    resolved_variable_map: &FxHashMap<&str, Vec<Toplevel<'a>>>,
) -> (
    Vec<(IdentId, VariableId)>,
    IncompleteType<'a, SccTypeConstructor<'a>>,
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
        resolved_idents
            .push((ident_id, satisfied.id_of_satisfied_variable));
        scc = satisfied.type_of_improved_decl;
    }
    (resolved_idents, scc)
}

fn constructor_type(d: DataDecl) -> TypeUnit {
    let field_types: Vec<_> =
        (0..d.field_len).map(|_| TypeUnit::new_variable()).collect();
    let mut t = TypeUnit::Normal {
        name: d.name,
        args: field_types.iter().map(|t| t.clone().into()).collect(),
        id: TypeId::DeclId(d.decl_id),
    };
    for field in field_types.into_iter().rev() {
        t = TypeUnit::Fn(field.into(), t.into())
    }
    t
}

fn min_type<'a>(
    expr: &Expr<'a>,
) -> Result<(IncompleteType<'a>, Resolved), &'a str> {
    Ok(min_type_incomplite(expr))
}

fn min_type_incomplite<'a>(
    expr: &Expr<'a>,
) -> (IncompleteType<'a>, Resolved) {
    match expr {
        Expr::Lambda(arms) => {
            let (
                arm_types,
                variable_requirements,
                subtype_relation,
                resolved_idents,
            ): (Vec<_>, Vec<_>, Vec<_>, Vec<_>) =
                multiunzip(arms.iter().map(arm_min_type));
            let resolved_idents =
                resolved_idents.into_iter().flatten().collect();
            let (args, rtns): (
                Vec<types::Type<'a>>,
                Vec<types::Type<'a>>,
            ) = arm_types.into_iter().unzip();
            let constructor = if args.len() == 1 {
                TypeUnit::Fn(
                    args.into_iter().next().unwrap(),
                    rtns.into_iter().next().unwrap(),
                )
            } else {
                TypeUnit::Fn(
                    args.into_iter().flatten().collect(),
                    rtns.into_iter().flatten().collect(),
                )
            };
            (
                IncompleteType {
                    constructor: constructor.into(),
                    variable_requirements: variable_requirements
                        .concat(),
                    subtype_relation: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                },
                resolved_idents,
            )
        }
        Expr::Number(_) => {
            (construct_type("Num").into(), Default::default())
        }
        Expr::StrLiteral(_) => {
            (construct_type("String").into(), Default::default())
        }
        Expr::Ident {
            name: info,
            ident_id,
            ..
        } => {
            let t: types::Type = TypeUnit::new_variable().into();
            (
                IncompleteType {
                    constructor: t.clone(),
                    variable_requirements: vec![(info, t, *ident_id)],
                    subtype_relation: BTreeSet::new(),
                },
                Default::default(),
            )
        }
        Expr::Decl(_) => {
            (construct_type("()").into(), Default::default())
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1) = min_type_incomplite(f);
            let (a_t, resolved2) = min_type_incomplite(a);
            let b: types::Type = TypeUnit::new_variable().into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn = TypeUnit::Fn(c.clone(), b.clone());
            // f < c -> b
            let f_sub_cb = [(f_t.constructor, cb_fn.into())]
                .iter()
                .cloned()
                .collect();
            // a < c
            let a_sub_c =
                [(a_t.constructor, c)].iter().cloned().collect();
            (
                IncompleteType {
                    constructor: b,
                    variable_requirements: [
                        f_t.variable_requirements,
                        a_t.variable_requirements,
                    ]
                    .concat(),
                    subtype_relation: vec![
                        f_sub_cb,
                        a_sub_c,
                        f_t.subtype_relation,
                        a_t.subtype_relation,
                    ]
                    .into_iter()
                    .flatten()
                    .collect(),
                },
                [resolved1, resolved2].concat(),
            )
        }
    }
}

fn multi_expr_min_type<'a>(
    exprs: &[Expr<'a>],
) -> (IncompleteType<'a>, Resolved) {
    let mut variable_requirements = Vec::new();
    let mut subtype_relation = BTreeSet::new();
    let mut resolved_idents = Vec::default();
    let t = exprs
        .iter()
        .map(|e| {
            let (t, resolved) = min_type_incomplite(e);
            variable_requirements
                .append(&mut t.variable_requirements.clone());
            subtype_relation.extend(t.subtype_relation.clone());
            resolved_idents.extend(resolved);
            t
        })
        .collect::<Vec<_>>();
    let t = t.last().unwrap().clone();
    (
        IncompleteType {
            constructor: t.constructor,
            variable_requirements,
            subtype_relation,
        },
        resolved_idents,
    )
}

type VariableRequirement<'a> = (&'a str, types::Type<'a>, IdentId);
type SubtypeRelation<'a> =
    BTreeSet<(types::Type<'a>, types::Type<'a>)>;

/// Returns (argument type, return type), variable requirements, subtype relation, resolved idents.
fn arm_min_type<'a>(
    arm: &FnArm<'a>,
) -> (
    (types::Type<'a>, types::Type<'a>),
    Vec<VariableRequirement<'a>>,
    SubtypeRelation<'a>,
    Resolved,
) {
    let (body_type, mut resolved_idents) =
        multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).unzip();
    let mut arm_type = body_type.constructor;
    let mut types = types.into_iter();
    let first_type = types.next().unwrap();
    for pattern_type in types.rev() {
        arm_type = TypeUnit::Fn(pattern_type, arm_type).into()
    }
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
            resolved_idents.push((p.2, VariableId::Decl(a.0)));
        } else {
            variable_requirements.push(p);
        }
    }
    (
        (first_type, arm_type),
        variable_requirements,
        {
            let mut tmp = body_type.subtype_relation;
            tmp.append(
                &mut subtype_requirement.into_iter().collect(),
            );
            tmp
        },
        resolved_idents,
    )
}

fn pattern_to_type<'a>(
    p: &Pattern<'a>,
) -> (types::Type<'a>, Vec<(&'a str, DeclId, types::Type<'a>)>) {
    match p {
        Pattern::Number(_) => (construct_type("Num"), Vec::new()),
        Pattern::StrLiteral(_) => {
            (construct_type("String"), Vec::new())
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
