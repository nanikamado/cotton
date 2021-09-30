use crate::ast1::{IncompleteType, Requirements, Type};
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Display,
    vec,
};

struct SubtypeOrd<'a>(&'a Type);

impl PartialOrd for SubtypeOrd<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;
        match (self <= other, other <= self) {
            (true, true) => Some(Equal),
            (true, false) => Some(Less),
            (false, true) => Some(Greater),
            (false, false) => None,
        }
    }
    fn le(&self, other: &Self) -> bool {
        use Type::*;
        match (self.0, other.0) {
            (Normal(n1, cs1), Normal(n2, cs2)) => {
                debug_assert_eq!(cs1.len(), cs2.len());
                n1 == n2
                    && cs1.iter().zip(cs2).all(|(c1, c2)| {
                        SubtypeOrd(c1) <= SubtypeOrd(c2)
                    })
            }
            (Fn(a1, r1), Fn(a2, r2)) => r1 <= r2 && a2 <= a1,
            (Union(u), _) => {
                u.iter().all(|c| SubtypeOrd(c) <= *other)
            }
            (_, Union(u)) => {
                u.contains(self.0)
                    || u.iter().any(|c| *self <= SubtypeOrd(c))
            }
            (Anonymous(a), Anonymous(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialEq for SubtypeOrd<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

pub fn simplify_type(
    mut t: IncompleteType,
    fixed_variables: &HashMap<String, Type>,
) -> Option<IncompleteType> {
    // eprintln!("{}", t);
    let mut t_ = _simplify_type(t.clone(), fixed_variables)?;
    let mut lim = 100;
    while t != t_ {
        t = t_.clone();
        // eprintln!("{}", t);
        t_ = _simplify_type(t_, fixed_variables)?;
        lim -= 1;
        if lim == 0 {
            eprintln!("loop count reached the limit.");
            break;
        }
    }
    Some(t_)
}

fn _simplify_type(
    t: IncompleteType,
    fixed_variables: &HashMap<String, Type>,
) -> Option<IncompleteType> {
    use Type::*;
    let mut subtype_relationship = t.requirements.subtype_relation;
    let variable_requirements: Vec<(String, Type)> = t
        .requirements
        .variable_requirements
        .into_iter()
        .filter(|(name, req_type)| {
            if let Some(fixed) = fixed_variables.get(name) {
                let fixed = fixed.clone().change_anonymous_num();
                subtype_relationship
                    .insert((fixed.clone(), req_type.clone()));
                subtype_relationship
                    .insert((req_type.clone(), fixed));
                false
            } else {
                true
            }
        })
        .collect();
    let g = mk_graph(&subtype_relationship);
    let eq_types = tarjan_scc(&g);
    let mut t = IncompleteType {
        constructor: t.constructor,
        requirements: Requirements {
            variable_requirements,
            subtype_relation: subtype_relationship.clone(),
        },
    };
    // eprintln!("105: {}", &t);
    for eqs in eq_types {
        let (eq_anonymous, eq_cons): (Vec<_>, Vec<_>) = eqs
            .into_iter()
            .map(|ts| {
                if let Anonymous(n) = ts {
                    Ok(*n)
                } else {
                    Err(ts)
                }
            })
            .partition_result();
        if eq_cons.is_empty() {
            for a in &eq_anonymous[1..] {
                t = t.replace_num_option(
                    *a,
                    &Anonymous(eq_anonymous[0]),
                )?;
            }
        } else {
            for a in eq_anonymous {
                t = t.replace_num_option(a, eq_cons[0])?;
            }
        }
    }
    t.requirements.subtype_relation = t
        .requirements
        .subtype_relation
        .into_iter()
        .map(|(a, b)| deconstruct_subtype_rel(a, b))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect();
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
    let anonymous_types_in_sub_rel: HashSet<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .flat_map(|(a, b)| {
            let mut a = a.all_anonymous_types();
            a.extend(b.all_anonymous_types());
            a
        })
        .collect();
    for a in &anonymous_types_in_sub_rel {
        let st =
            possible_strongest(*a, &t.requirements.subtype_relation);
        let we =
            possible_weakest(*a, &t.requirements.subtype_relation);
        match (st, we) {
            (Some(st), Some(we)) if st == we => {
                t = t.replace_num_option(*a, &st)?
            }
            _ => (),
        }
    }
    for (a, b) in t.requirements.subtype_relation.clone() {
        match (a, b) {
            (Anonymous(a), Fn(_, _)) => {
                let new_fn_type = Fn(
                    Box::new(Type::new_variable()),
                    Box::new(Type::new_variable()),
                );
                t = t.replace_num_option(a, &new_fn_type.clone())?;
            }
            // (Normal(name, cs), Anonymous(n)) => {
            //     let new_type = Union(
            //         [
            //             Normal(name, cs),
            //             Type::new_variable(anonymous_type_count),
            //         ]
            //         .iter()
            //         .cloned()
            //         .collect(),
            //     );
            //     t = t.replace_num(n, &new_type);
            // }
            // (Fn(a, r), Anonymous(n)) => {
            //     let new_type = Union(
            //         [
            //             Fn(a, r),
            //             Type::new_variable(anonymous_type_count),
            //         ]
            //         .iter()
            //         .cloned()
            //         .collect(),
            //     );
            //     t = t.replace_num(n, &new_type);
            // }
            // (Anonymous(n), a) if a.is_singleton() => {
            //     let new_type =
            //         Union(vec![a, Empty].into_iter().collect());
            //     t = t.replace_num(n, &new_type);
            // }
            _ => (),
        }
    }
    Some(t)
}

fn deconstruct_subtype_rel(
    sub: Type,
    sup: Type,
) -> Option<Vec<(Type, Type)>> {
    use Type::*;
    match (sub, sup) {
        (Union(cs), b) => Some(
            cs.into_iter()
                .map(|c| deconstruct_subtype_rel(c, b.clone()))
                .collect::<Option<Vec<_>>>()?
                .concat(),
        ),
        (Fn(a1, r1), Fn(a2, r2)) => Some(
            [
                deconstruct_subtype_rel(*r1, *r2)?,
                deconstruct_subtype_rel(*a2, *a1)?,
            ]
            .concat(),
        ),
        (Normal(n1, cs1), Normal(n2, cs2)) => {
            if n1 == n2 {
                assert_eq!(cs1.len(), cs2.len());
                Some(
                    cs1.into_iter()
                        .zip(cs2)
                        .map(|(a, b)| deconstruct_subtype_rel(a, b))
                        .collect::<Option<Vec<_>>>()?
                        .concat(),
                )
            } else {
                eprintln!("{} != {}", n1, n2);
                None
            }
        }
        (Empty, _) => Some(Vec::new()),
        (Anonymous(a), Anonymous(b)) if a == b => Some(Vec::new()),
        (a, Union(u)) if u.contains(&a) => Some(Vec::new()),
        (a, Union(u)) if u.len() == 1 => {
            deconstruct_subtype_rel(a, u.into_iter().next().unwrap())
        }
        (a, Union(mut u)) if u.contains(&Empty) => {
            u.remove(&Empty);
            deconstruct_subtype_rel(a, Union(u))
        }
        (a, Union(cs)) if a.is_singleton() => {
            let new_cs: BTreeSet<Type> = cs
                .into_iter()
                .filter(|c| !(c.is_singleton() && a != *c))
                .collect();
            Some(vec![(a, Union(new_cs))])
        }
        (sub, sup) => Some(vec![(sub, sup)]),
    }
}

fn possible_weakest(
    t: usize,
    subtype_relation: &BTreeSet<(Type, Type)>,
) -> Option<Type> {
    let mut up = Vec::new();
    for (sub, sup) in subtype_relation {
        if anonymous_contravariant_types(sup).contains(&t) {
            return None;
        } else if *sub == Type::Anonymous(t) {
            up.push(sup);
        } else if anonymous_covariant_types(sub).contains(&t) {
            return None;
        }
    }
    if up.len() == 1 {
        Some(up[0].clone())
    } else if up.is_empty() {
        eprintln!("{} -> Any", t);
        Some(Type::Normal("Any".to_string(), Vec::new()))
    } else {
        let upc = up
            .iter()
            .filter(|t| {
                matches!(t, Type::Fn(_, _) | Type::Normal(_, _))
            })
            .collect_vec();
        if upc.len() == 1 {
            Some((**upc[0]).clone())
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
        if anonymous_contravariant_types(sub).contains(&t) {
            return None;
        } else if *sup == Type::Anonymous(t) {
            down.push(sub);
        } else if anonymous_covariant_types(sup).contains(&t) {
            return None;
        }
    }
    if down.len() == 1 {
        Some(down[0].clone())
    } else if down.is_empty() {
        Some(Type::Empty)
    } else {
        Some(Type::union_from(down.into_iter().cloned()))
    }
}

fn mk_contravariant_candidates(t: &IncompleteType) -> HashSet<usize> {
    let mut rst: HashSet<usize> =
        anonymous_contravariant_types(&t.constructor)
            .into_iter()
            .collect();
    for (_, v) in &t.requirements.variable_requirements {
        rst.extend(anonymous_covariant_types(v));
    }
    rst
}

fn mk_covariant_candidates(t: &IncompleteType) -> HashSet<usize> {
    let mut rst: HashSet<usize> =
        anonymous_covariant_types(&t.constructor)
            .into_iter()
            .collect();
    for (_, v) in &t.requirements.variable_requirements {
        rst.extend(anonymous_contravariant_types(v));
    }
    rst
}

fn anonymous_covariant_types(t: &Type) -> Vec<usize> {
    match t {
        Type::Fn(a, r) => [
            anonymous_covariant_types(r),
            anonymous_contravariant_types(a),
        ]
        .concat(),
        Type::Normal(_, cs) => {
            cs.iter().map(|c| anonymous_covariant_types(c)).concat()
        }
        Type::Union(cs) => {
            cs.iter().map(|c| anonymous_covariant_types(c)).concat()
        }
        Type::Anonymous(n) => vec![*n],
        Type::Empty => Vec::new(),
    }
}

fn anonymous_contravariant_types(t: &Type) -> Vec<usize> {
    match t {
        Type::Fn(a, r) => [
            anonymous_covariant_types(a),
            anonymous_contravariant_types(r),
        ]
        .concat(),
        Type::Normal(_, cs) => cs
            .iter()
            .map(|c| anonymous_contravariant_types(c))
            .concat(),
        Type::Union(cs) => cs
            .iter()
            .map(|c| anonymous_contravariant_types(c))
            .concat(),
        Type::Anonymous(_) | Type::Empty => Vec::new(),
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
                        deconstruct_subtype_rel(a, b)
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
            && self.requirements.subtype_relation.is_empty()
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
    assert_eq!(
        Anonymous(0).replace_num(0, &Anonymous(1)),
        Anonymous(1)
    );
}

#[test]
fn replace_type_test1() {
    use Type::*;
    assert_eq!(
        Fn(Box::new(Anonymous(0)), Box::new(Anonymous(2)))
            .replace_num(0, &Anonymous(1)),
        Fn(Box::new(Anonymous(1)), Box::new(Anonymous(2)))
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
            Anonymous(n) => write!(f, "t{}", n),
            Empty => write!(f, "∅"),
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
