use crate::ast1::{
    types::{Type, TypeMatchable, TypeMatchableRef, TypeUnit},
    IncompleteType, Requirements,
};
use fxhash::FxHashSet;
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{collections::BTreeSet, fmt::Display, iter::Extend, vec};

pub fn simplify_type(
    mut t: IncompleteType,
) -> Option<IncompleteType> {
    let mut i = 0;
    loop {
        i += 1;
        let r = _simplify_type(t)?;
        t = r.0;
        let updated = r.1;
        if !updated {
            debug_assert_eq!(t, _simplify_type(t.clone()).unwrap().0);
            break;
        } else if i > 10 {
            log::debug!("loop count reached the limit.");
            break;
        }
    }
    log::debug!("loop: {}", i);
    Some(t)
}

fn _simplify_type(
    mut t: IncompleteType,
) -> Option<(IncompleteType, bool)> {
    use TypeUnit::*;
    let hash_before_simplify = fxhash::hash(&t);
    let subtype_relationship =
        t.requirements.subtype_relation.clone();
    let g = mk_graph(&subtype_relationship);
    let eq_types = tarjan_scc(&g);
    for eqs in eq_types {
        let (eq_variable, eq_cons): (Vec<_>, Vec<_>) = eqs
            .into_iter()
            .map(|ts| {
                if let TypeMatchableRef::Variable(n) =
                    ts.matchable_ref()
                {
                    Ok(n)
                } else {
                    Err(ts)
                }
            })
            .partition_result();
        if eq_cons.is_empty() {
            for a in &eq_variable[1..] {
                t = t.replace_num_option(
                    *a,
                    &Variable(eq_variable[0]).into(),
                )?;
            }
        } else {
            for a in eq_variable {
                t = t.replace_num_option(a, eq_cons[0])?;
            }
        }
    }
    t.requirements.subtype_relation = t
        .requirements
        .subtype_relation
        .into_iter()
        .map(|(a, b)| simplify_subtype_rel(a, b))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect();
    t.constructor = lift_recursive_alias(t.constructor);
    for cov in mk_covariant_candidates(&t) {
        if !mk_contravariant_candidates(&t).contains(&cov) {
            if let Some(s) = possible_strongest(
                cov,
                &t.requirements.subtype_relation,
            ) {
                t = t.replace_num_option(cov, &s)?;
            }
        }
    }
    for cont in mk_contravariant_candidates(&t) {
        if !mk_covariant_candidates(&t).contains(&cont) {
            if let Some(s) = possible_weakest(
                cont,
                &t.requirements.subtype_relation,
            ) {
                t = t.replace_num_option(cont, &s)?;
            }
        }
    }
    let type_variables_in_sub_rel: FxHashSet<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .flat_map(|(a, b)| {
            let mut a = a.all_type_variables();
            a.extend(b.all_type_variables());
            a
        })
        .collect();
    for a in &type_variables_in_sub_rel {
        let st =
            possible_strongest(*a, &t.requirements.subtype_relation);
        let we =
            possible_weakest(*a, &t.requirements.subtype_relation);
        match (st, we) {
            (Some(st), Some(we)) if st == we => {
                t = t.replace_num_option(*a, &st)?;
            }
            (_, Some(we)) if we.len() == 0 => {
                t = t.replace_num_option(
                    *a,
                    &TypeMatchable::Empty.into(),
                )?;
            }
            // (Some(st), _)
            //     if !covariant_candidates.contains(a)
            //         && !contravariant_candidates.contains(a)
            //         && st != Type::Empty =>
            // {
            //     let new_type =
            //         Type::union_with(st, Type::new_variable());
            //     t = t.replace_num_option(*a, &new_type)?
            // }
            _ => (),
        }
    }
    let covariant_candidates = mk_covariant_candidates(&t);
    let contravariant_candidates = mk_contravariant_candidates(&t);
    let type_variables_in_sub_rel: HashBag<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .flat_map(|(a, b)| {
            let mut a = a.all_type_variables();
            a.extend(b.all_type_variables());
            a
        })
        .collect();
    t.requirements.subtype_relation = t
        .requirements
        .subtype_relation
        .into_iter()
        .filter(|(_, a)| {
            if let TypeMatchableRef::Variable(a) = a.matchable_ref() {
                contravariant_candidates.contains(&a)
                    || covariant_candidates.contains(&a)
                    || type_variables_in_sub_rel.contains(&a) >= 2
            } else {
                true
            }
        })
        .collect();
    let updated = fxhash::hash(&t) != hash_before_simplify;
    Some((t, updated))
}

fn simplify_subtype_rel(
    sub: Type,
    sup: Type,
) -> Option<Vec<(Type, Type)>> {
    use TypeMatchable::*;
    match (sub.matchable(), sup.matchable()) {
        (Union(cs), b) => Some(
            cs.into_iter()
                .map(|c| {
                    simplify_subtype_rel(c.into(), b.clone().into())
                })
                .collect::<Option<Vec<_>>>()?
                .concat(),
        ),
        (Fn(a1, r1), Fn(a2, r2)) => Some(
            [
                simplify_subtype_rel(r1, r2)?,
                simplify_subtype_rel(a2, a1)?,
            ]
            .concat(),
        ),
        (Normal(n1, cs1), Normal(n2, cs2)) => {
            if n1 == n2 {
                assert_eq!(cs1.len(), cs2.len());
                Some(
                    cs1.into_iter()
                        .zip(cs2)
                        .map(|(a, b)| simplify_subtype_rel(a, b))
                        .collect::<Option<Vec<_>>>()?
                        .concat(),
                )
            } else {
                None
            }
        }
        (Fn(_, _), Normal(_, _))
        | (Normal(_, _), Fn(_, _))
        | (Fn(_, _), Empty)
        | (Normal(_, _), Empty) => None,
        (sub, sup) if sub == sup => Some(Vec::new()),
        (Empty, _) => Some(Vec::new()),
        (a, Union(u)) if u.contains(&a.clone().into()) => {
            Some(Vec::new())
        }
        (a, RecursiveAlias { alias: _, body })
            if body.contains(&a.clone().into()) =>
        {
            Some(Vec::new())
        }
        (Normal(name, cs), RecursiveAlias { alias, body }) => {
            simplify_subtype_rel(
                Normal(name, cs).into(),
                unwrap_recursive_alias(alias, body),
            )
        }
        (
            RecursiveAlias {
                alias: alias1,
                body: body1,
            },
            RecursiveAlias {
                alias: alias2,
                body: body2,
            },
        ) if body1
            == body2.clone().replace_num(
                alias2,
                &TypeUnit::Variable(alias1).into(),
            ) =>
        {
            Some(Vec::new())
        }
        (a, Union(cs)) if Type::from(a.clone()).is_singleton() => {
            let new_cs = cs
                .into_iter()
                .filter(|c| {
                    !(c.is_singleton()
                        && Type::from(a.clone())
                            != Type::from(c.clone()))
                })
                .collect();
            Some(vec![(a.into(), new_cs)])
        }
        (Normal(name, cs), Union(u)) => {
            let new_u: Type = u
                .into_iter()
                .filter(|c| {
                    if let TypeUnit::Normal(c_name, _) = c {
                        *c_name == name
                    } else {
                        true
                    }
                })
                .collect();
            Some(vec![(TypeUnit::Normal(name, cs).into(), new_u)])
        }
        (sub, sup) => {
            let sub: Type = sub.into();
            let sup: Type = sup.into();
            let subl = lift_recursive_alias(sub.clone());
            let supl = lift_recursive_alias(sup.clone());
            if subl != sub || supl != sup {
                simplify_subtype_rel(subl, supl)
            } else {
                Some(vec![(subl, supl)])
            }
        }
    }
}

fn lift_recursive_alias(t: Type) -> Type {
    if let Some((alias, body)) = t.find_recursive_alias() {
        let r = &TypeUnit::RecursiveAlias {
            alias,
            body: body.clone(),
        };
        let t = t.replace_type(r, &TypeUnit::Variable(alias));
        let t =
            t.replace_type_union(&body, &TypeUnit::Variable(alias));
        t.replace_num(alias, &r.clone().into())
    } else {
        t
    }
}

fn unwrap_recursive_alias(alias: usize, body: Type) -> Type {
    body.clone().replace_num(
        alias,
        &(TypeUnit::RecursiveAlias { alias, body }).into(),
    )
}

impl TypeUnit {
    fn find_recursive_alias(&self) -> Option<(usize, Type)> {
        match self {
            TypeUnit::Normal(_, cs) => {
                cs.iter().find_map(Type::find_recursive_alias)
            }
            TypeUnit::Fn(a, r) => {
                a.find_recursive_alias()?;
                r.find_recursive_alias()
            }
            TypeUnit::Variable(_) => None,
            TypeUnit::RecursiveAlias { alias, body } => {
                Some((*alias, body.clone()))
            }
        }
    }
}

impl Type {
    fn find_recursive_alias(&self) -> Option<(usize, Type)> {
        self.iter().find_map(TypeUnit::find_recursive_alias)
    }
}

fn possible_weakest(
    t: usize,
    subtype_relation: &BTreeSet<(Type, Type)>,
) -> Option<Type> {
    let mut up = FxHashSet::default();
    for (sub, sup) in subtype_relation {
        if contravariant_type_variables(sup).contains(&t) {
            return None;
        } else if *sub == TypeUnit::Variable(t).into() {
            up.insert(sup);
        } else if covariant_type_variables(sub).contains(&t) {
            return None;
        }
    }
    if up.len() == 1 {
        let up = up.into_iter().next().unwrap().clone();
        Some(if up.contains_num(t) {
            let v = TypeUnit::new_variable_num();
            TypeUnit::RecursiveAlias {
                alias: v,
                body: up
                    .replace_num(t, &TypeUnit::Variable(v).into()),
            }
            .into()
        } else {
            up
        })
    } else if up.is_empty() {
        None
    } else {
        let up_fs: FxHashSet<_> = up
            .iter()
            .filter(|t| {
                matches!(
                    t.matchable_ref(),
                    TypeMatchableRef::Fn(_, _)
                )
            })
            .collect();
        let up_ns: FxHashSet<_> = up
            .iter()
            .filter_map(|t| {
                if let TypeMatchableRef::Normal(name, _) =
                    t.matchable_ref()
                {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();
        if !up_fs.is_empty() && !up_ns.is_empty() || up_ns.len() > 1 {
            Some(TypeMatchable::Empty.into())
        } else {
            None
        }
    }
}

fn possible_strongest(
    t: usize,
    subtype_relation: &BTreeSet<(Type, Type)>,
) -> Option<Type> {
    let mut down = Vec::new();
    for (sub, sup) in subtype_relation {
        if contravariant_type_variables(sub).contains(&t) {
            return None;
        } else if *sup == TypeUnit::Variable(t).into() {
            down.push(sub);
        } else if covariant_type_variables(sup).contains(&t) {
            return None;
        }
    }

    let result = if down.len() == 1 {
        down[0].clone()
    } else if down.is_empty() {
        TypeMatchable::Empty.into()
    } else {
        down.iter().copied().cloned().flatten().collect()
    };
    if down.iter().any(|d| d.contains_num(t)) {
        let v = TypeUnit::new_variable_num();
        Some(
            TypeUnit::RecursiveAlias {
                alias: v,
                body: result
                    .replace_num(t, &TypeUnit::Variable(v).into()),
            }
            .into(),
        )
    } else {
        Some(result)
    }
}

fn mk_contravariant_candidates(
    t: &IncompleteType,
) -> FxHashSet<usize> {
    let mut rst: FxHashSet<usize> =
        contravariant_type_variables(&t.constructor)
            .into_iter()
            .collect();
    for (_, v, _) in &t.requirements.variable_requirements {
        rst.extend(covariant_type_variables(v));
    }
    rst
}

fn mk_covariant_candidates(t: &IncompleteType) -> FxHashSet<usize> {
    let mut rst: FxHashSet<usize> =
        covariant_type_variables(&t.constructor)
            .into_iter()
            .collect();
    for (_, v, _) in &t.requirements.variable_requirements {
        rst.extend(contravariant_type_variables(v));
    }
    rst
}

fn covariant_type_variables(t: &Type) -> FxHashSet<usize> {
    match t.matchable_ref() {
        TypeMatchableRef::Fn(a, r) => marge_hashset(
            covariant_type_variables(r),
            contravariant_type_variables(a),
        ),
        TypeMatchableRef::Normal(_, cs) => {
            cs.iter().flat_map(covariant_type_variables).collect()
        }
        TypeMatchableRef::Union(cs) => cs
            .iter()
            .map(|c| covariant_type_variables(&c.clone().into()))
            .concat(),
        TypeMatchableRef::Variable(n) => {
            [n].iter().copied().collect()
        }
        TypeMatchableRef::Empty => FxHashSet::default(),
        TypeMatchableRef::RecursiveAlias { alias, body } => {
            let mut vs = covariant_type_variables(body);
            vs.remove(&alias);
            vs
        }
    }
}

fn marge_hashset<T>(
    mut a: FxHashSet<T>,
    b: FxHashSet<T>,
) -> FxHashSet<T>
where
    T: Eq + core::hash::Hash,
{
    a.extend(b);
    a
}

fn contravariant_type_variables(t: &Type) -> FxHashSet<usize> {
    match t.matchable_ref() {
        TypeMatchableRef::Fn(a, r) => marge_hashset(
            covariant_type_variables(a),
            contravariant_type_variables(r),
        ),
        TypeMatchableRef::Normal(_, cs) => {
            cs.iter().map(contravariant_type_variables).concat()
        }
        TypeMatchableRef::Union(cs) => cs
            .iter()
            .map(|c| contravariant_type_variables(&c.clone().into()))
            .concat(),
        TypeMatchableRef::Variable(_) | TypeMatchableRef::Empty => {
            FxHashSet::default()
        }
        TypeMatchableRef::RecursiveAlias { alias, body } => {
            let mut vs = contravariant_type_variables(body);
            vs.remove(&alias);
            vs
        }
    }
}

impl IncompleteType {
    pub fn replace_num_option(
        self,
        from: usize,
        to: &Type,
    ) -> Option<Self> {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation: subtype_relationship,
                },
        } = self;
        Some(IncompleteType {
            constructor: constructor.replace_num(from, to),
            requirements: Requirements {
                variable_requirements: variable_requirements
                    .into_iter()
                    .map(|(name, t, id)| {
                        (name, t.replace_num(from, to), id)
                    })
                    .collect(),
                subtype_relation: subtype_relationship
                    .into_iter()
                    .map(|(a, b)| {
                        let a = a.replace_num(from, to);
                        let b = b.replace_num(from, to);
                        simplify_subtype_rel(a, b)
                    })
                    .collect::<Option<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .collect(),
            },
        })
    }

    pub fn resolved(&self) -> bool {
        self.requirements.variable_requirements.is_empty()
    }
}

fn mk_graph(
    subtype_relationship: &BTreeSet<(Type, Type)>,
) -> DiGraphMap<&Type, ()> {
    let mut g = DiGraphMap::new();
    for (a, b) in subtype_relationship {
        g.add_edge(a, b, ());
    }
    g
}

#[test]
fn replace_type_test0() {
    use TypeUnit::*;
    assert_eq!(
        Variable(0).replace_num(0, &Variable(1).into()),
        Variable(1).into()
    );
}

#[test]
fn replace_type_test1() {
    use TypeUnit::*;
    assert_eq!(
        Fn(Variable(0).into(), Variable(2).into())
            .replace_num(0, &Variable(1).into()),
        Fn(Variable(1).into(), Variable(2).into()).into()
    );
}

impl Display for IncompleteType {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} forall\n{}--",
            self.constructor, self.requirements
        )
    }
}

impl Display for Requirements {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        for (a, b) in &self.subtype_relation {
            writeln!(f, "    {} < {},", a, b)?;
        }
        for (a, b, _) in &self.variable_requirements {
            writeln!(f, "    ?{} : {},", a, b)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use stripmargin::StripMargin;

    use crate::{
        ast1::{IncompleteType, Requirements},
        type_check::{
            simplify::simplify_type,
            type_util::{
                construct_type, construct_type_with_variables,
            },
        },
    };

    #[test]
    fn simplify1() {
        let req_t_s = "Num /\\ Num -> \
                   ((Num /\\ Num | Num /\\ t1 | t2 /\\ Num | t3 /\\ t4) -> Num | String)\
                   -> Num | String";
        let req_t = construct_type_with_variables(
            req_t_s,
            &["t1", "t2", "t3", "t4"],
        );
        let dot = construct_type_with_variables(
            "a -> (a -> b) -> b",
            &["a", "b"],
        );
        let t = IncompleteType {
            constructor: construct_type("Num -> Num | String"),
            requirements: Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: vec![(dot, req_t)]
                    .into_iter()
                    .collect(),
            },
        };
        let st = simplify_type(t).unwrap();
        assert_eq!(
            format!("{}", st.requirements),
            r"|    /\(Num, Num) < t4,
              |    t4 < {/\(Num, Num) | /\(Num, t0) | /\(t1, Num) | /\(t2, t3)},
              |"
            .strip_margin()
        );
    }
}
