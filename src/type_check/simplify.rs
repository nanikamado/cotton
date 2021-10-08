use crate::ast1::{IncompleteType, Requirements, Type};
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
            break;
        } else if i > 10 {
            eprintln!("loop count reached the limit.");
            break;
        }
    }
    eprintln!("loop: {}", i);
    Some(t)
}

fn _simplify_type(
    mut t: IncompleteType,
) -> Option<(IncompleteType, bool)> {
    use Type::*;
    let mut updated = false;
    let subtype_relationship =
        t.requirements.subtype_relation.clone();
    let g = mk_graph(&subtype_relationship);
    let eq_types = tarjan_scc(&g);
    for eqs in eq_types {
        let (eq_variable, eq_cons): (Vec<_>, Vec<_>) = eqs
            .into_iter()
            .map(|ts| {
                if let Variable(n) = ts {
                    Ok(*n)
                } else {
                    Err(ts)
                }
            })
            .partition_result();
        if eq_variable.len() >= 2
            || !eq_variable.is_empty() && !eq_cons.is_empty()
        {
            updated = true;
        }
        if eq_cons.is_empty() {
            for a in &eq_variable[1..] {
                t = t.replace_num_option(
                    *a,
                    &Variable(eq_variable[0]),
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
                updated = true;
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
                updated = true;
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
                updated = true;
            }
            (_, Some(Type::Empty)) => {
                t = t.replace_num_option(*a, &Type::Empty)?;
                updated = true;
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
            if let Variable(a) = a {
                let b = contravariant_candidates.contains(a)
                    || covariant_candidates.contains(a)
                    || type_variables_in_sub_rel.contains(a) >= 2;
                if !b {
                    updated = true;
                }
                b
            } else {
                true
            }
        })
        .collect();
    Some((t, updated))
}

fn simplify_subtype_rel(
    sub: Type,
    sup: Type,
) -> Option<Vec<(Type, Type)>> {
    use Type::*;
    match (sub, sup) {
        (Union(cs), b) => Some(
            cs.into_iter()
                .map(|c| simplify_subtype_rel(c, b.clone()))
                .collect::<Option<Vec<_>>>()?
                .concat(),
        ),
        (Fn(a1, r1), Fn(a2, r2)) => Some(
            [
                simplify_subtype_rel(*r1, *r2)?,
                simplify_subtype_rel(*a2, *a1)?,
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
                // eprintln!("{} != {}", n1, n2);
                None
            }
        }
        (Fn(_, _), Normal(_, _))
        | (Normal(_, _), Fn(_, _))
        | (Fn(_, _), Empty)
        | (Normal(_, _), Empty) => None,
        (sub, sup) if sub == sup => Some(Vec::new()),
        (Empty, _) => Some(Vec::new()),
        (a, Union(u)) if u.contains(&a) => Some(Vec::new()),
        (a, RecursiveAlias { alias: _, body })
            if (if let Union(u) = &*body {
                u.contains(&a)
            } else {
                false
            }) =>
        {
            Some(Vec::new())
        }
        (Normal(name, cs), RecursiveAlias { alias, body }) => {
            simplify_subtype_rel(
                Normal(name, cs),
                unwrap_recursive_alias(alias, *body),
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
        ) if *body1
            == body2
                .clone()
                .replace_num(alias2, &Type::Variable(alias1)) =>
        {
            Some(Vec::new())
        }
        (a, Union(cs)) if a.is_singleton() => {
            let new_cs = cs
                .into_iter()
                .filter(|c| !(c.is_singleton() && a != *c))
                .collect();
            Some(vec![(a, new_cs)])
        }
        (Normal(name, cs), Union(u)) => {
            let new_u: Type = u
                .into_iter()
                .filter(|c| {
                    if let Normal(c_name, _) = c {
                        *c_name == name
                    } else {
                        true
                    }
                })
                .collect();
            Some(vec![(Normal(name, cs), new_u)])
        }
        (sub, sup) => {
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
    if let Some((alias, body)) = find_recursive_alias(&t) {
        let r = &Type::RecursiveAlias {
            alias,
            body: Box::new(body.clone()),
        };
        let t = t.replace_type(r, &Type::Variable(alias));
        let t = t.replace_type(&body, &Type::Variable(alias));
        t.replace_num(alias, r)
    } else {
        t
    }
}

fn unwrap_recursive_alias(alias: usize, body: Type) -> Type {
    body.clone().replace_num(
        alias,
        &Type::RecursiveAlias {
            alias,
            body: Box::new(body),
        },
    )
}

fn find_recursive_alias(t: &Type) -> Option<(usize, Type)> {
    match t {
        Type::Normal(_, cs) => {
            cs.iter().find_map(find_recursive_alias)
        }
        Type::Fn(a, r) => {
            [a, r].iter().find_map(|c| find_recursive_alias(c))
        }
        Type::Union(u) => u.iter().find_map(find_recursive_alias),
        Type::Variable(_) => None,
        Type::Empty => None,
        Type::RecursiveAlias { alias, body } => {
            Some((*alias, (**body).clone()))
        }
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
        } else if *sub == Type::Variable(t) {
            up.insert(sup);
        } else if covariant_type_variables(sub).contains(&t) {
            return None;
        }
    }
    if up.len() == 1 {
        let up = up.into_iter().next().unwrap().clone();
        Some(if up.contains(t) {
            let v = Type::new_variable_num();
            Type::RecursiveAlias {
                alias: v,
                body: Box::new(up.replace_num(t, &Type::Variable(v))),
            }
        } else {
            up
        })
    } else if up.is_empty() {
        // eprintln!("{} -> Any", t);
        // if let Type::Variable(n) = Type::new_variable() {
        //     Some(Type::Variable(n + 10000))
        // } else {
        //     unreachable!()
        // }
        None
    } else {
        let up_fs: FxHashSet<_> = up
            .iter()
            .filter(|t| matches!(t, Type::Fn(_, _)))
            .collect();
        let up_ns: FxHashSet<_> = up
            .iter()
            .filter_map(|t| {
                if let Type::Normal(name, _) = t {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();
        if !up_fs.is_empty() && !up_ns.is_empty() || up_ns.len() > 1 {
            Some(Type::Empty)
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
        } else if *sup == Type::Variable(t) {
            down.push(sub);
        } else if covariant_type_variables(sup).contains(&t) {
            return None;
        }
    }

    let result = if down.len() == 1 {
        down[0].clone()
    } else if down.is_empty() {
        Type::Empty
    } else {
        down.iter().copied().cloned().collect()
    };
    if down.iter().any(|d| d.contains(t)) {
        let v = Type::new_variable_num();
        Some(Type::RecursiveAlias {
            alias: v,
            body: Box::new(result.replace_num(t, &Type::Variable(v))),
        })
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
    for (_, v) in &t.requirements.variable_requirements {
        rst.extend(covariant_type_variables(v));
    }
    rst
}

fn mk_covariant_candidates(t: &IncompleteType) -> FxHashSet<usize> {
    let mut rst: FxHashSet<usize> =
        covariant_type_variables(&t.constructor)
            .into_iter()
            .collect();
    for (_, v) in &t.requirements.variable_requirements {
        rst.extend(contravariant_type_variables(v));
    }
    rst
}

fn covariant_type_variables(t: &Type) -> FxHashSet<usize> {
    match t {
        Type::Fn(a, r) => marge_hashset(
            covariant_type_variables(r),
            contravariant_type_variables(a),
        ),
        Type::Normal(_, cs) => cs
            .iter()
            .flat_map(|c| covariant_type_variables(c))
            .collect(),
        Type::Union(cs) => {
            cs.iter().map(|c| covariant_type_variables(c)).concat()
        }
        Type::Variable(n) => [*n].iter().copied().collect(),
        Type::Empty => FxHashSet::default(),
        Type::RecursiveAlias { alias, body } => {
            let mut vs = covariant_type_variables(body);
            vs.remove(alias);
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
    match t {
        Type::Fn(a, r) => marge_hashset(
            covariant_type_variables(a),
            contravariant_type_variables(r),
        ),
        Type::Normal(_, cs) => cs
            .iter()
            .map(|c| contravariant_type_variables(c))
            .concat(),
        Type::Union(cs) => cs
            .iter()
            .map(|c| contravariant_type_variables(c))
            .concat(),
        Type::Variable(_) | Type::Empty => FxHashSet::default(),
        Type::RecursiveAlias { alias, body } => {
            let mut vs = contravariant_type_variables(body);
            vs.remove(alias);
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
                    .map(|(name, t)| (name, t.replace_num(from, to)))
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
    use Type::*;
    assert_eq!(Variable(0).replace_num(0, &Variable(1)), Variable(1));
}

#[test]
fn replace_type_test1() {
    use Type::*;
    assert_eq!(
        Fn(Box::new(Variable(0)), Box::new(Variable(2)))
            .replace_num(0, &Variable(1)),
        Fn(Box::new(Variable(1)), Box::new(Variable(2)))
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

impl Display for Type {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use Type::*;
        match self {
            Normal(name, cs) => {
                if cs.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        cs.iter()
                            .map(|c| format!("{}", c))
                            .join(", ")
                    )
                }
            }
            Fn(arg, rtn) => {
                if let Fn(_, _) = **arg {
                    write!(f, "({}) -> {}", arg, rtn)
                } else {
                    write!(f, "{} -> {}", arg, rtn)
                }
            }
            Union(a) => write!(
                f,
                "{{{}}}",
                a.iter()
                    .map(|t| {
                        if let Fn(_, _) = t {
                            format!("({})", t)
                        } else {
                            format!("{}", t)
                        }
                    })
                    .join(" | ")
            ),
            Variable(n) => write!(f, "t{}", n),
            Empty => write!(f, "∅"),
            RecursiveAlias { alias, body } => {
                write!(f, "rec[t{} = {}]", alias, *body)
            }
        }
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
        for (a, b) in &self.variable_requirements {
            writeln!(f, "    ?{} : {},", a, b)?;
        }
        Ok(())
    }
}
