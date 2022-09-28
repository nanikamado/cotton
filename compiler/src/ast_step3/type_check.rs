mod simplify;

pub use self::simplify::{simplify_subtype_rel, TypeVariableMap};
use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        ident_id::IdentId,
        types::{self, SingleTypeConstructor, TypeMatchable},
        types::{Type, TypeUnit, TypeVariable},
        Ast, DataDecl, Expr, ExprWithType, FnArm, IncompleteType, Pattern,
        PatternRestrictions, PatternUnit, PatternUnitForRestriction,
        SubtypeRelations, TypeId,
    },
    ast_step4::VariableKind,
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

pub type ResolvedIdents<'a> = FxHashMap<IdentId, ResolvedIdent<'a>>;

pub fn type_check<'a>(
    ast: &Ast<'a>,
) -> (
    ResolvedIdents<'a>,
    FxHashMap<VariableId, ast_step2::IncompleteType<'a>>,
    FxHashMap<VariableId, Type<'a>>,
    SubtypeRelations<'a>,
    TypeVariableMap<'a>,
) {
    let mut toplevels: Vec<Toplevel<'a>> = Default::default();
    for v in IntrinsicVariable::iter() {
        toplevels.push(Toplevel {
            incomplete: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicVariable(v),
            name: v.to_str(),
            variables_required_by_interface_restrictions: Default::default(),
            variable_kind: VariableKind::Intrinsic,
        });
    }
    for v in IntrinsicConstructor::iter() {
        toplevels.push(Toplevel {
            incomplete: v.to_type().clone().into(),
            type_annotation: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::IntrinsicConstructor(v),
            name: v.to_str(),
            variables_required_by_interface_restrictions: Default::default(),
            variable_kind: VariableKind::IntrinsicConstructor,
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
            variables_required_by_interface_restrictions: Default::default(),
            variable_kind: VariableKind::Constructor,
        });
    }
    let mut resolved_idents = Vec::new();
    let mut subtype_relations = SubtypeRelations::default();
    let mut map = TypeVariableMap::default();
    let mut types_of_local_decls = Vec::new();
    for d in &ast.variable_decl {
        let (mut t, resolved, mut tod) =
            min_type_incomplete(&d.value, &mut subtype_relations, &mut map);
        resolved_idents.extend(resolved);
        types_of_local_decls.append(&mut tod);
        let type_annotation: Option<ast_step2::IncompleteType> =
            if let Some(annotation) = &d.type_annotation {
                t.subtype_relations.insert((
                    t.constructor.clone(),
                    annotation.constructor.clone(),
                ));
                t.subtype_relations
                    .extend(annotation.subtype_relations.clone());
                t.variable_requirements
                    .append(&mut annotation.variable_requirements.clone());
                Some(annotation.clone())
            } else {
                None
            };
        let vs: FxHashMap<_, _> = d
            .implicit_parameters
            .iter()
            .map(|(s, t, decl_id)| (*s, (t, decl_id)))
            .collect();
        let mut suptype_rel = Vec::new();
        t.variable_requirements = t
            .variable_requirements
            .into_iter()
            .filter_map(|mut req| {
                if let Some((t, decl_id)) = vs.get(req.name) {
                    suptype_rel.push(((*t).clone(), req.required_type.clone()));
                    resolved_idents.push((
                        req.ident,
                        ResolvedIdent {
                            variable_id: VariableId::Decl(**decl_id),
                            type_args: Default::default(),
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
        let incomplete = simplify::simplify_type(
            &mut map,
            IncompleteType {
                constructor: SingleTypeConstructor {
                    type_: t.constructor,
                    contravariant_candidates_from_annotation: type_annotation
                        .as_ref()
                        .map(|t| t.constructor.contravariant_type_variables()),
                },
                variable_requirements: t.variable_requirements,
                subtype_relations: t.subtype_relations,
                pattern_restrictions: t.pattern_restrictions,
                already_considered_relations: t.already_considered_relations,
            },
        )
        .unwrap();
        subtype_relations =
            subtype_relations.merge(incomplete.subtype_relations.clone());
        toplevels.push(Toplevel {
            incomplete: incomplete.into(),
            type_annotation,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
            name: d.name,
            variables_required_by_interface_restrictions: d
                .implicit_parameters
                .clone(),
            variable_kind: VariableKind::Global,
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
    let (mut resolved_names, types, rel) = resolve_names(toplevels, &mut map);
    subtype_relations = subtype_relations.merge(rel);
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
                    type_args,
                    implicit_args,
                    variable_kind,
                },
            )| {
                (
                    ident_id,
                    ResolvedIdent {
                        variable_id,
                        type_args: type_args
                            .into_iter()
                            .map(|(v, t)| (v, map.normalize_type(t)))
                            .collect(),
                        implicit_args: implicit_args
                            .into_iter()
                            .map(|(decl_id, name, t, r)| {
                                (decl_id, name, map.normalize_type(t), r)
                            })
                            .collect(),
                        variable_kind,
                    },
                )
            },
        )
        .collect();
    log::debug!("ok");
    (
        resolved_idents,
        types
            .into_iter()
            .map(|(d, t)| {
                (
                    d,
                    t.map_type(|t| lift_recursive_alias(map.normalize_type(t))),
                )
            })
            .collect(),
        types_of_local_decls
            .into_iter()
            .map(|(d, t)| (d, lift_recursive_alias(map.normalize_type(t))))
            .collect(),
        subtype_relations,
        map,
    )
}

/// Change `Cons[List[a], a] | Nil` to `List[a]`
fn lift_recursive_alias<'a, T>(t: T) -> T
where
    T: TypeConstructor<'a>,
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
pub struct ResolvedIdent<'a> {
    pub variable_id: VariableId,
    pub type_args: Vec<(TypeVariable, Type<'a>)>,
    pub variable_kind: VariableKind,
    pub implicit_args: Vec<(DeclId, &'a str, Type<'a>, ResolvedIdent<'a>)>,
}

pub type Resolved<'a> = Vec<(IdentId, ResolvedIdent<'a>)>;

#[derive(Debug, Clone)]
struct Toplevel<'a> {
    incomplete: ast_step2::IncompleteType<'a>,
    type_annotation: Option<ast_step2::IncompleteType<'a>>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
    name: &'a str,
    variables_required_by_interface_restrictions:
        Vec<(&'a str, Type<'a>, DeclId)>,
    variable_kind: VariableKind,
}

type TypesOfLocalDeclsVec<'a> = Vec<(VariableId, ast_step2::types::Type<'a>)>;
type TypesOfGlobalDeclsVec<'a> =
    Vec<(VariableId, ast_step2::IncompleteType<'a>)>;

fn resolve_names<'a>(
    toplevels: Vec<Toplevel<'a>>,
    map: &mut TypeVariableMap<'a>,
) -> (
    Resolved<'a>,
    TypesOfGlobalDeclsVec<'a>,
    SubtypeRelations<'a>,
) {
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
                .flat_map(|req| &toplevle_map[req.name])
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
                simplify::simplify_type(map, improved_type.clone()).unwrap()
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
        .collect();
    (resolved_idents, types, rel)
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct SccTypeConstructor<'a>(Vec<SingleTypeConstructor<'a>>);

impl Display for SccTypeConstructor<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.0.iter().join(", "))?;
        write!(f, "]")
    }
}

impl<'a> Type<'a> {
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
}

impl<'a> PatternUnitForRestriction<'a> {
    fn argument_tuple_from_arguments(ps: Vec<Self>) -> Self {
        let mut new_p = PatternUnitForRestriction::Const {
            id: TypeId::Intrinsic(IntrinsicType::Unit),
            name: "()",
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
        self.replace_num_with_update_flag(from, to, 0).0
    }

    fn replace_num_with_update_flag(
        self,
        from: TypeVariable,
        to: &Type<'a>,
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

    fn find_recursive_alias(&self) -> Option<&Type<'a>> {
        self.0
            .iter()
            .find_map(TypeConstructor::find_recursive_alias)
    }

    fn replace_type(self, from: &TypeUnit<'a>, to: &TypeUnit<'a>) -> Self {
        SccTypeConstructor(
            self.0
                .into_iter()
                .map(|t| t.replace_type(from, to))
                .collect(),
        )
    }

    fn replace_type_union(self, from: &Type, to: &TypeUnit<'a>) -> Self {
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

    fn map_type<F: FnMut(Type<'a>) -> Type<'a>>(self, mut f: F) -> Self {
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
    ) -> Option<Self> {
        Some(Self(
            self.0
                .into_iter()
                .map(|s| {
                    s.normalize_contravariant_candidates_from_annotation(map)
                })
                .collect::<Option<_>>()?,
        ))
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
    Resolved<'a>,
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
        subtype_relations.extend(t.incomplete.subtype_relations.clone());
        types.push(SingleTypeConstructor {
            type_: t.incomplete.constructor.clone(),
            contravariant_candidates_from_annotation: t
                .type_annotation
                .as_ref()
                .map(|t| t.constructor.contravariant_type_variables()),
        });
        pattern_restrictions.extend(t.incomplete.pattern_restrictions.clone())
    }
    let names_in_scc: FxHashSet<_> = name_vec.iter().copied().collect();
    log::debug!("name of unresolved: {:?}", names_in_scc);
    // The order of resolving is important.
    // Requirements that are easier to solve should be solved earlier.
    variable_requirements.sort_unstable_by_key(|req| {
        (
            !names_in_scc.contains(req.name),
            resolved_variable_map.get(req.name).map(|v| {
                Reverse(
                    v.iter()
                        .map(|d| {
                            d.variables_required_by_interface_restrictions.len()
                                + 1
                        })
                        .sum::<usize>(),
                )
            }),
        )
    });
    let mut unresolved_type = IncompleteType {
        constructor: SccTypeConstructor(types),
        variable_requirements,
        subtype_relations,
        pattern_restrictions,
        already_considered_relations: Default::default(),
    };
    // Recursions are not resolved in this loop.
    while let Some(req) = unresolved_type.variable_requirements.pop() {
        if names_in_scc.contains(req.name) {
            unresolved_type.variable_requirements.push(req);
            // Skipping the resolveing of recursion.
            break;
        }
        let satisfied = find_satisfied_types(
            &req,
            &unresolved_type,
            resolved_variable_map,
            map,
            &names_in_scc,
        );
        let satisfied = get_one_satisfied(satisfied);
        resolved_idents.push((
            req.ident,
            ResolvedIdent {
                variable_id: satisfied.id_of_satisfied_variable,
                type_args: satisfied.type_args.clone(),
                implicit_args: satisfied.implicit_args,
                variable_kind: satisfied.variable_kind,
            },
        ));
        *map = satisfied.map;
        unresolved_type = satisfied.type_of_improved_decl;
        map.insert_type(
            &mut unresolved_type.subtype_relations,
            req.required_type,
            satisfied.type_of_satisfied_variable,
        );
    }
    // Resolve recursive requirements.
    let (mut resolved, improved_types) = resolve_recursion_in_scc(
        unresolved_type,
        &scc,
        resolved_variable_map,
        map,
        &names_in_scc,
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
                        variable_requirements: variable_requirements.clone(),
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
    variable_kind: VariableKind,
    type_of_improved_decl: T,
    type_args: Vec<(TypeVariable, Type<'a>)>,
    implicit_args: Vec<(DeclId, &'a str, Type<'a>, ResolvedIdent<'a>)>,
    map: TypeVariableMap<'a>,
}

trait CandidatesProvider<'a>: Copy {
    type T: Iterator<Item = Candidate<'a>>;
    fn get_candidates(self, req_name: &str) -> Self::T;
}

impl<'a> CandidatesProvider<'a> for &FxHashMap<&str, Vec<Toplevel<'a>>> {
    type T = std::vec::IntoIter<Candidate<'a>>;

    fn get_candidates(self, req_name: &str) -> Self::T {
        self.get(req_name)
            .into_iter()
            .flatten()
            .cloned()
            .map(|t| Candidate {
                candidate: t,
                replace_variables: true,
            })
            .collect_vec()
            .into_iter()
    }
}

#[derive(Debug, Clone, Copy)]
struct CandidatesProviderWithFn<'a, 'b, F: FnMut(usize) -> Candidate<'a>> {
    scc_map: &'b FxHashMap<&'b str, Vec<usize>>,
    f: F,
}

impl<'a, 'b, F: FnMut(usize) -> Candidate<'a> + Copy> CandidatesProvider<'a>
    for CandidatesProviderWithFn<'a, 'b, F>
{
    type T = std::iter::Map<std::vec::IntoIter<usize>, F>;

    fn get_candidates(self, req_name: &str) -> Self::T {
        self.scc_map
            .get(req_name)
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
struct Candidate<'a> {
    candidate: Toplevel<'a>,
    replace_variables: bool,
}

#[derive(Debug, Clone, Copy)]
struct CandidatesProviderForScc<'a, 'b, F: FnMut(usize) -> Candidate<'a>> {
    candidates_provider_with_fn: CandidatesProviderWithFn<'a, 'b, F>,
    normal_map: &'b FxHashMap<&'b str, Vec<Toplevel<'a>>>,
}

impl<'a, 'b, F: FnMut(usize) -> Candidate<'a> + Copy> CandidatesProvider<'a>
    for CandidatesProviderForScc<'a, 'b, F>
{
    type T = std::iter::Chain<
        std::vec::IntoIter<Candidate<'a>>,
        std::iter::Map<std::vec::IntoIter<usize>, F>,
    >;

    fn get_candidates(self, req_name: &str) -> Self::T {
        self.normal_map
            .get_candidates(req_name)
            .chain(self.candidates_provider_with_fn.get_candidates(req_name))
    }
}

fn find_satisfied_types<
    'a,
    T: TypeConstructor<'a>,
    C: CandidatesProvider<'a>,
>(
    req: &VariableRequirement<'a>,
    type_of_unresolved_decl: &IncompleteType<'a, T>,
    resolved_variable_map: C,
    map: &TypeVariableMap<'a>,
    names_in_scc: &FxHashSet<&str>,
) -> Vec<SatisfiedType<'a, IncompleteType<'a, T>>> {
    log::trace!("type_of_unresolved_decl:");
    log::trace!("{}", type_of_unresolved_decl);
    log::trace!("required_type : {}", req.required_type);
    resolved_variable_map
        .get_candidates(req.name)
        .filter_map(
            |Candidate {
                 candidate,
                 replace_variables,
             }| {
                let mut t = type_of_unresolved_decl.clone();
                let mut cand_t = if let Some(face) = candidate.type_annotation {
                    face
                } else {
                    candidate.incomplete
                };
                let mut type_args = Vec::new();
                let mut map = map.clone();
                log::debug!("~~ {} : {}", candidate.name, cand_t);
                for (req_name, req_t, decl_id) in
                    &candidate.variables_required_by_interface_restrictions
                {
                    log::debug!("   {} : {} ({})", req_name, req_t, decl_id);
                }
                let mut implicit_args = Vec::new();
                let mut resolved_implicit_args = FxHashMap::default();
                for (interface_v_name, interface_v_t, interface_v_decl_id) in
                    candidate.variables_required_by_interface_restrictions
                {
                    let arg = IdentId::new();
                    implicit_args.push((
                        interface_v_decl_id,
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
                                type_args: Default::default(),
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
                if replace_variables {
                    cand_t = cand_t.normalize(&mut map).unwrap();
                    (cand_t, type_args) = cand_t.change_variable_num();
                }
                t.subtype_relations.add_subtype_rel(
                    cand_t.constructor.clone(),
                    req.required_type.clone(),
                );
                t.subtype_relations.add_subtype_rel(
                    req.required_type.clone(),
                    cand_t.constructor.clone(),
                );
                t.subtype_relations
                    .add_subtype_rels(cand_t.subtype_relations);
                t.variable_requirements
                    .extend(cand_t.variable_requirements.clone());
                let decl_id = candidate.decl_id;
                simplify::simplify_type(&mut map, t).map(
                    |mut type_of_improved_decl| {
                        while let Some(req) = cand_t.variable_requirements.pop()
                        {
                            if names_in_scc.contains(req.name) {
                                type_of_improved_decl
                                    .variable_requirements
                                    .push(req);
                                // Skipping the resolveing of recursion.
                                panic!();
                                // break;
                            }
                            let satisfied = find_satisfied_types(
                                &req,
                                &type_of_improved_decl,
                                resolved_variable_map,
                                &map,
                                names_in_scc,
                            );
                            let satisfied = get_one_satisfied(satisfied);
                            resolved_implicit_args.insert(
                                req.ident,
                                ResolvedIdent {
                                    variable_id: satisfied
                                        .id_of_satisfied_variable,
                                    type_args: satisfied.type_args,
                                    implicit_args: satisfied.implicit_args,
                                    variable_kind: satisfied.variable_kind,
                                },
                            );
                            map = satisfied.map;
                            type_of_improved_decl =
                                satisfied.type_of_improved_decl;
                            map.insert_type(
                                &mut type_of_improved_decl.subtype_relations,
                                req.required_type,
                                satisfied.type_of_satisfied_variable,
                            );
                        }
                        SatisfiedType {
                            id_of_satisfied_variable: decl_id,
                            type_of_improved_decl,
                            type_args,
                            implicit_args: implicit_args
                                .into_iter()
                                .map(|(decl_id, name, t, ident_id)| {
                                    (
                                        decl_id,
                                        name,
                                        t,
                                        resolved_implicit_args[&ident_id]
                                            .clone(),
                                    )
                                })
                                .collect(),
                            type_of_satisfied_variable: cand_t.constructor,
                            map,
                            variable_kind: candidate.variable_kind,
                        }
                    },
                )
            },
        )
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
                        s.id_of_satisfied_variable, s.type_of_improved_decl
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
    names_in_scc: &FxHashSet<&str>,
) -> (Resolved<'a>, IncompleteType<'a, SccTypeConstructor<'a>>) {
    let mut scc_map: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
    for (i, t) in toplevels.iter().enumerate() {
        scc_map.entry(t.name).or_default().push(i);
    }
    let mut resolved_idents = Vec::new();
    while let Some(req) = scc.variable_requirements.pop() {
        let satisfied = find_satisfied_types(
            &req,
            &scc,
            CandidatesProviderForScc {
                candidates_provider_with_fn: CandidatesProviderWithFn {
                    scc_map: &scc_map,
                    f: |j| Candidate {
                        candidate: Toplevel {
                            incomplete: scc.constructor.0[j]
                                .type_
                                .clone()
                                .into(),
                            ..toplevels[j].clone()
                        },
                        replace_variables: false,
                    },
                },
                normal_map: resolved_variable_map,
            },
            map,
            names_in_scc,
        );
        let satisfied = get_one_satisfied(satisfied);
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
                type_args: satisfied.type_args,
                implicit_args: satisfied.implicit_args,
                variable_kind: satisfied.variable_kind,
            },
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
    let mut t = TypeUnit::Tuple(
        TypeUnit::Const {
            name: d.name,
            id: TypeId::DeclId(d.decl_id),
        }
        .into(),
        Type::argument_tuple_from_arguments(fields.clone()),
    );
    for field in fields.into_iter().rev() {
        t = TypeUnit::Fn(field, t.into())
    }
    t
}

fn min_type_incomplete<'a>(
    (expr, type_variable): &ExprWithType<'a, TypeVariable>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> (
    ast_step2::IncompleteType<'a>,
    Resolved<'a>,
    TypesOfLocalDeclsVec<'a>,
) {
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
                ast_step2::IncompleteType {
                    constructor,
                    variable_requirements: variable_requirements.concat(),
                    subtype_relations: subtype_relation
                        .into_iter()
                        .flatten()
                        .collect(),
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
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
                ast_step2::IncompleteType {
                    constructor: t.clone(),
                    variable_requirements: vec![VariableRequirement {
                        name,
                        required_type: t,
                        ident: *ident_id,
                        local_env: Default::default(),
                    }],
                    subtype_relations: SubtypeRelations::default(),
                    pattern_restrictions: PatternRestrictions::default(),
                    already_considered_relations: Default::default(),
                },
                Default::default(),
                Default::default(),
            )
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1, types_of_decls_f) =
                min_type_incomplete(f, subtype_relations, map);
            let (a_t, resolved2, types_of_decls_a) =
                min_type_incomplete(a, subtype_relations, map);
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
                        min_type_incomplete(e, &mut subtype_relations, map);
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
                ast_step2::IncompleteType {
                    constructor: t.constructor,
                    variable_requirements,
                    subtype_relations,
                    pattern_restrictions,
                    already_considered_relations: Default::default(),
                },
                resolved_idents,
                types_of_decls,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct VariableRequirement<'a> {
    pub name: &'a str,
    pub required_type: Type<'a>,
    pub ident: IdentId,
    pub local_env: Vec<(&'a str, DeclId, Type<'a>)>,
}

/// Returns `vec![argument type, argument type, ..., return type]`,
/// variable requirements, subtype relation, resolved idents.
fn arm_min_type<'a>(
    arm: &FnArm<'a, TypeVariable>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> (
    Vec<types::Type<'a>>,
    Vec<PatternUnitForRestriction<'a>>,
    Vec<VariableRequirement<'a>>,
    SubtypeRelations<'a>,
    Resolved<'a>,
    PatternRestrictions<'a>,
    TypesOfLocalDeclsVec<'a>,
) {
    let (body_type, mut resolved_idents, mut types_of_decls) =
        min_type_incomplete(&arm.expr, subtype_relations, map);
    let (mut ts, bindings, patterns): (Vec<_>, Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).multiunzip();
    ts.push(body_type.constructor);
    let bindings: FxHashMap<&str, (DeclId, types::Type)> = bindings
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
                    type_args: Vec::new(),
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

fn pattern_unit_to_type<'a>(
    p: &PatternUnit<'a, TypeVariable>,
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
        Constructor { name, id, args } => {
            let (types, bindings, pattern_restrictions): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = args.iter().map(pattern_to_type).multiunzip();
            (
                TypeUnit::Tuple(
                    TypeUnit::Const {
                        name,
                        id: (*id).into(),
                    }
                    .into(),
                    Type::argument_tuple_from_arguments(types),
                )
                .into(),
                // TypeUnit::new_variable().into(),
                bindings.into_iter().flatten().collect(),
                PatternUnitForRestriction::Tuple(
                    PatternUnitForRestriction::Const {
                        name,
                        id: (*id).into(),
                    }
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

fn pattern_to_type<'a>(
    p: &Pattern<'a, TypeVariable>,
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
