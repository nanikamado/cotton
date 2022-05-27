mod simplify;

use super::type_util::construct_type;
use crate::{
    ast2::{
        decl_id::DeclId,
        ident_id::IdentId,
        types,
        types::{Type, TypeUnit},
        Ast, DataDecl, Expr, FnArm, IncompleteType, Pattern,
        Requirements, TypeId,
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

#[derive(PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
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

pub fn type_check(ast: &Ast) -> FxHashMap<IdentId, VariableId> {
    let mut toplevels: Vec<Toplevel> = Default::default();
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
            t.requirements.subtype_relation.insert((
                t.constructor.clone(),
                annotation.constructor.clone(),
            ));
            t.requirements.subtype_relation.insert((
                annotation.constructor.clone(),
                t.constructor.clone(),
            ));
            t.requirements =
                t.requirements.merge(annotation.requirements.clone());
            Some(annotation)
        } else {
            None
        };
        toplevels.push(Toplevel {
            incomplete: simplify::simplify_type(t.clone()).unwrap(),
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
    let resolved_names = resolve_names(toplevels);
    for (ident_id, variable_id) in
        resolved_names.iter().sorted_unstable()
    {
        log::debug!("{ident_id} => {variable_id}");
    }
    resolved_idents.extend(resolved_names);
    resolved_idents
}

#[derive(Debug, Clone)]
struct Toplevel<'a> {
    incomplete: IncompleteType<'a>,
    type_annotation: Option<IncompleteType<'a>>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: &'a str,
}

fn resolve_names(
    toplevels: Vec<Toplevel>,
) -> Vec<(IdentId, VariableId)> {
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
                .requirements
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
    resolved_idents
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
    fn all_type_variables(&self) -> FxHashSet<usize> {
        self.0
            .iter()
            .flat_map(TypeConstructor::all_type_variables)
            .collect()
    }

    fn replace_num(self, from: usize, to: &Type<'a>) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_num(from, to))
                .collect(),
        )
    }

    fn covariant_type_variables(&self) -> Vec<usize> {
        self.0
            .iter()
            .flat_map(TypeConstructor::covariant_type_variables)
            .collect()
    }

    fn contravariant_type_variables(&self) -> Vec<usize> {
        self.0
            .iter()
            .flat_map(TypeConstructor::contravariant_type_variables)
            .collect()
    }

    fn find_recursive_alias(&self) -> Option<(usize, Type<'a>)> {
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
        variable_requirements.append(
            &mut t
                .incomplete
                .requirements
                .variable_requirements
                .clone(),
        );
        subtype_relation.extend(
            t.incomplete.requirements.subtype_relation.clone(),
        );
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
        requirements: Requirements {
            variable_requirements,
            subtype_relation,
        },
    };
    // Recursions are not resolved in this loop.
    while let Some((req_name, req_type, ident_id)) =
        unresolved_type.requirements.variable_requirements.pop()
    {
        if names_in_scc.contains(req_name) {
            unresolved_type
                .requirements
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
    let reqs = improved_types.requirements;
    (
        resolved_idents,
        improved_types
            .constructor
            .0
            .into_iter()
            .map(|t| IncompleteType {
                constructor: t,
                requirements: reqs.clone(),
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
            t.requirements
                .subtype_relation
                .insert((cand_t.constructor, required_type.clone()));
            t.requirements
                .subtype_relation
                .extend(cand_t.requirements.subtype_relation);
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
        scc.requirements.variable_requirements.pop()
    {
        let mut satisfied = find_satisfied_types(
            &scc,
            &req_type,
            resolved_variable_map
                .get(req_name)
                .into_iter()
                .cloned()
                .flatten(),
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
        id: TypeId::DeclId(d.decl_id, d.name),
    };
    for field in field_types.into_iter().rev() {
        t = TypeUnit::Fn(field.into(), t.into())
    }
    t
}

fn min_type<'a>(
    expr: &'a Expr,
) -> Result<(IncompleteType<'a>, Resolved), &'a str> {
    Ok(min_type_incomplite(expr))
}

fn min_type_incomplite<'a>(
    expr: &'a Expr,
) -> (IncompleteType<'a>, Resolved) {
    match expr {
        Expr::Lambda(arms) => {
            let (arm_types, requirements, resolved_idents): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = multiunzip(arms.iter().map(arm_min_type));
            let resolved_idents =
                resolved_idents.into_iter().flatten().collect();
            let (args, rtns): (Vec<types::Type>, Vec<types::Type>) =
                arm_types.into_iter().unzip();
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
                    requirements: marge_requirements(requirements),
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
                    requirements: Requirements {
                        variable_requirements: vec![(
                            info, t, *ident_id,
                        )],
                        subtype_relation: BTreeSet::new(),
                    },
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
            let f_sub_cb = Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: {
                    [(f_t.constructor, cb_fn.into())]
                        .iter()
                        .cloned()
                        .collect()
                },
            };
            // a < c
            let a_sub_c = Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: [(a_t.constructor, c)]
                    .iter()
                    .cloned()
                    .collect(),
            };
            (
                IncompleteType {
                    constructor: b,
                    requirements: marge_requirements(vec![
                        f_sub_cb,
                        a_sub_c,
                        f_t.requirements,
                        a_t.requirements,
                    ]),
                },
                [resolved1, resolved2].concat(),
            )
        }
    }
}

fn multi_expr_min_type<'a>(
    exprs: &'a [Expr],
) -> (IncompleteType<'a>, Resolved) {
    let mut req = Requirements::default();
    let mut resolved_idents = Vec::default();
    let t = exprs
        .iter()
        .map(|e| {
            let (t, resolved) = min_type_incomplite(e);
            resolved_idents.extend(resolved);
            req = marge_requirements(vec![
                req.clone(),
                t.clone().requirements,
            ]);
            t
        })
        .collect::<Vec<_>>();
    let t = t.last().unwrap().clone();
    (
        IncompleteType {
            constructor: t.constructor,
            requirements: req,
        },
        resolved_idents,
    )
}

fn marge_requirements(
    requirements: Vec<Requirements>,
) -> Requirements {
    let mut rst = Requirements::default();
    for mut r in requirements {
        rst.variable_requirements
            .append(&mut r.variable_requirements);
        rst.subtype_relation.append(&mut r.subtype_relation);
    }
    rst
}

fn arm_min_type<'a>(
    arm: &'a FnArm,
) -> (
    (types::Type<'a>, types::Type<'a>),
    Requirements<'a>,
    Resolved,
) {
    let (body_type, mut resolved_idents) =
        multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type = TypeUnit::Fn(pattern_type.clone(), arm_type).into()
    }
    let bindings: FxHashMap<&str, (DeclId, types::Type)> = bindings
        .into_iter()
        .flatten()
        .map(|(n, i, t)| (n, (i, t)))
        .collect();
    let mut variable_requirements = Vec::new();
    let mut subtype_requirement = Vec::new();
    for p in body_type.requirements.variable_requirements.into_iter()
    {
        if let Some(a) = bindings.get(&p.0) {
            subtype_requirement.push((a.1.clone(), p.1.clone()));
            subtype_requirement.push((p.1, a.1.clone()));
            resolved_idents.push((p.2, VariableId::Decl(a.0)));
        } else {
            variable_requirements.push(p);
        }
    }
    (
        (types[0].clone(), arm_type),
        Requirements {
            variable_requirements,
            subtype_relation: {
                let mut tmp = body_type.requirements.subtype_relation;
                tmp.append(
                    &mut subtype_requirement.into_iter().collect(),
                );
                tmp
            },
        },
        resolved_idents,
    )
}

fn pattern_to_type<'a>(
    p: &'a Pattern,
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

// #[cfg(test)]
// mod tests {
//     use super::Toplevel;
//     use crate::{
//         ast1, ast2,
//         ast2::{
//             decl_id::{self, new_decl_id},
//             ident_id::new_ident_id,
//             IncompleteType, Requirements,
//         },
//         ast3::{
//             type_check::{resolve_names, VariableId},
//             type_util::construct_type_with_variables,
//         },
//         parse,
//     };
//     use fxhash::FxHashMap;
//     use std::collections::BTreeSet;
//     use stripmargin::StripMargin;

//     #[test]
//     fn resolve_1() {
//         let ast: ast1::Ast =
//             parse::parse("data Hoge\ndata Fuga\nmain = ()")
//                 .unwrap()
//                 .1
//                 .into();
//         let ast: ast2::Ast = ast.into();
//         let data_decl_map: FxHashMap<&str, decl_id::DeclId> = ast
//             .data_decl
//             .iter()
//             .map(|d| (&d.name[..], d.decl_id))
//             .collect();
//         let top_levels: FxHashMap<&str, Vec<Toplevel>> = vec![
//             (
//                 ("main"),
//                 vec![Toplevel {
//                     incomplete: IncompleteType {
//                         constructor: construct_type_with_variables(
//                             "()",
//                             &[],
//                             &data_decl_map,
//                         ),
//                         requirements: Requirements {
//                             variable_requirements: vec![
//                                 (
//                                     "default",
//                                     construct_type_with_variables(
//                                         "Hoge",
//                                         &[],
//                                         &data_decl_map,
//                                     ),
//                                     new_ident_id(),
//                                 ),
//                                 (
//                                     "default",
//                                     construct_type_with_variables(
//                                         "Fuga",
//                                         &[],
//                                         &data_decl_map,
//                                     ),
//                                     new_ident_id(),
//                                 ),
//                             ],
//                             subtype_relation: BTreeSet::new(),
//                         },
//                     },
//                     face: None,
//                     resolved_idents: Default::default(),
//                     decl_id: VariableId::Decl(new_decl_id()),
//                 }],
//             ),
//             (
//                 ("default"),
//                 vec![
//                     (Toplevel {
//                         incomplete: IncompleteType {
//                             constructor:
//                                 construct_type_with_variables(
//                                     "Hoge",
//                                     &[],
//                                     &data_decl_map,
//                                 ),
//                             requirements: Default::default(),
//                         },
//                         face: None,
//                         resolved_idents: Default::default(),
//                         decl_id: VariableId::Decl(new_decl_id()),
//                     }),
//                     (Toplevel {
//                         incomplete: IncompleteType {
//                             constructor:
//                                 construct_type_with_variables(
//                                     "Fuga",
//                                     &[],
//                                     &data_decl_map,
//                                 ),
//                             requirements: Default::default(),
//                         },
//                         face: None,
//                         resolved_idents: Default::default(),
//                         decl_id: VariableId::Decl(new_decl_id()),
//                     }),
//                 ],
//             ),
//         ]
//         .into_iter()
//         .collect();
//         let s = debug_toplevels(resolve_names(top_levels));
//         assert_eq!(
//             s,
//             "main :
//             |resolved: {IdentId(1): VariableId(4), IdentId(2): VariableId(5)}
//             |not face: () forall
//             |--
//             |default :
//             |resolved: {}
//             |not face: Hoge forall
//             |--
//             |resolved: {}
//             |not face: Fuga forall
//             |--
//             |"
//             .strip_margin()
//         );
//     }

//     #[test]
//     fn resolve_2() {
//         let ast: ast1::Ast =
//             parse::parse("data Hoge\ndata Fuga\nmain = ()")
//                 .unwrap()
//                 .1
//                 .into();
//         let ast: ast2::Ast = ast.into();
//         let data_decl_map: FxHashMap<&str, decl_id::DeclId> = ast
//             .data_decl
//             .iter()
//             .map(|d| (&d.name[..], d.decl_id))
//             .collect();
//         let top_levels: FxHashMap<&str, Vec<Toplevel>> = vec![
//             (
//                 ("main"),
//                 vec![Toplevel {
//                     incomplete: IncompleteType {
//                         constructor: construct_type_with_variables(
//                             "()",
//                             &[],
//                             &data_decl_map,
//                         ),
//                         requirements: Requirements {
//                             variable_requirements: vec![
//                                 (
//                                     "greet",
//                                     construct_type_with_variables(
//                                         "Hoge -> String",
//                                         &[],
//                                         &data_decl_map,
//                                     ),
//                                     new_ident_id(),
//                                 ),
//                                 (
//                                     "greet",
//                                     construct_type_with_variables(
//                                         "Fuga -> String",
//                                         &[],
//                                         &data_decl_map,
//                                     ),
//                                     new_ident_id(),
//                                 ),
//                             ],
//                             subtype_relation: BTreeSet::new(),
//                         },
//                     },
//                     face: None,
//                     resolved_idents: Default::default(),
//                     decl_id: VariableId::Decl(new_decl_id()),
//                 }],
//             ),
//             (
//                 ("greet"),
//                 vec![
//                     (Toplevel {
//                         incomplete: IncompleteType {
//                             constructor:
//                                 construct_type_with_variables(
//                                     "Hoge -> String",
//                                     &[],
//                                     &data_decl_map,
//                                 ),
//                             requirements: Default::default(),
//                         },
//                         face: None,
//                         resolved_idents: Default::default(),
//                         decl_id: VariableId::Decl(new_decl_id()),
//                     }),
//                     (Toplevel {
//                         incomplete: IncompleteType {
//                             constructor:
//                                 construct_type_with_variables(
//                                     "Fuga -> String",
//                                     &[],
//                                     &data_decl_map,
//                                 ),
//                             requirements: Default::default(),
//                         },
//                         face: None,
//                         resolved_idents: Default::default(),
//                         decl_id: VariableId::Decl(new_decl_id()),
//                     }),
//                 ],
//             ),
//         ]
//         .into_iter()
//         .collect();
//         let s = debug_toplevels(resolve_names(top_levels));
//         assert_eq!(
//             s,
//             r#"main :
//             |resolved: {IdentId(1): VariableId(4), IdentId(2): VariableId(5)}
//             |not face: () forall
//             |--
//             |greet :
//             |resolved: {}
//             |not face: Hoge -> String forall
//             |--
//             |resolved: {}
//             |not face: Fuga -> String forall
//             |--
//             |"#
//             .strip_margin()
//         );
//     }

//     fn debug_toplevels(
//         toplevels: FxHashMap<&str, Vec<Toplevel>>,
//     ) -> String {
//         let mut ret = String::new();
//         for (name, top) in &toplevels {
//             ret += &format!("{} : \n", name);
//             for t in top {
//                 ret +=
//                     &format!("resolved: {:?}\n", t.resolved_idents);
//                 if let Some(f) = &t.face {
//                     ret += &format!("face: {}\n", f);
//                     ret += &format!("incomplete: {}\n", t.incomplete);
//                 } else {
//                     ret += &format!("not face: {}\n", t.incomplete);
//                 }
//             }
//         }
//         ret
//     }
// }
