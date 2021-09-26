use crate::ast1;
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Display,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Normal(String, Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    Union(BTreeSet<Type>),
    Anonymous(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IncompleteType {
    pub constructor: Type,
    pub requirements: Requirements,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Requirements {
    variable_requirements: Vec<(String, Type)>,
    subtype_relation: BTreeSet<(Type, Type)>,
}

impl From<ast1::IncompleteType> for IncompleteType {
    fn from(i: ast1::IncompleteType) -> Self {
        IncompleteType {
            constructor: i.constructor.into(),
            requirements: i.requirements.into(),
        }
    }
}

impl From<ast1::Type> for Type {
    fn from(t: ast1::Type) -> Self {
        match t {
            ast1::Type::Normal(n, cs) => Type::Normal(
                n,
                cs.into_iter().map(|c| c.into()).collect(),
            ),
            ast1::Type::Fn(arms) => {
                let (args, rtns): (BTreeSet<Type>, BTreeSet<Type>) =
                    arms.into_iter()
                        .map(|ast1::FnArmType(a, r)| {
                            (a.into(), r.into())
                        })
                        .unzip();
                if args.len() == 1 {
                    Type::Fn(
                        Box::new(args.into_iter().next().unwrap()),
                        Box::new(rtns.into_iter().next().unwrap()),
                    )
                } else {
                    Type::Fn(
                        Box::new(Type::Union(args)),
                        Box::new(Type::Union(rtns)),
                    )
                }
            }
            ast1::Type::Union(_, _) => todo!(),
            ast1::Type::Anonymous(n) => Type::Anonymous(n),
        }
    }
}

impl From<ast1::Requirements> for Requirements {
    fn from(r: ast1::Requirements) -> Self {
        Requirements {
            variable_requirements: r
                .variable_requirements
                .into_iter()
                .map(|(n, t)| (n, t.into()))
                .collect(),
            subtype_relation: r
                .subtype_relationship
                .into_iter()
                .map(|(a, b)| (a.into(), b.into()))
                .collect(),
        }
    }
}

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
    anonymous_type_count: &mut usize,
) -> IncompleteType {
    // eprintln!("{}", t);
    let mut t_ = _simplify_type(
        t.clone(),
        fixed_variables,
        anonymous_type_count,
    );
    let mut lim = 100;
    while t != t_ {
        t = t_.clone();
        // eprintln!("{}", t);
        t_ =
            _simplify_type(t_, fixed_variables, anonymous_type_count);
        lim -= 1;
        if lim == 0 {
            eprintln!("loop count reached the limit.");
            break;
        }
    }
    t_
}

fn _simplify_type(
    t: IncompleteType,
    fixed_variables: &HashMap<String, Type>,
    anonymous_type_count: &mut usize,
) -> IncompleteType {
    use Type::*;
    let mut subtype_relationship = t.requirements.subtype_relation;
    let variable_requirements: Vec<(String, Type)> = t
        .requirements
        .variable_requirements
        .into_iter()
        .filter(|(name, req_type)| {
            if let Some(fixed) = fixed_variables.get(name) {
                let fixed = change_anonymous_num(
                    fixed.clone(),
                    anonymous_type_count,
                );
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
                t = t.replace_num(*a, &Anonymous(eq_anonymous[0]));
            }
        } else {
            for a in eq_anonymous {
                t = t.replace_num(a, eq_cons[0]);
            }
        }
    }
    let co_types: HashSet<usize> =
        anonymous_covariant_types(&t.constructor)
            .into_iter()
            .collect();
    let contra_types: HashSet<usize> =
        anonymous_contravariant_types(&t.constructor)
            .into_iter()
            .collect();
    let anonymous_types_in_sub_rel: HashBag<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .flat_map(|(a, b)| {
            [anonymous_types_in(a), anonymous_types_in(b)].concat()
        })
        .collect();
    let anonymous_types_in_cons: HashSet<usize> =
        anonymous_types_in(&t.constructor).into_iter().collect();
    let anonymous_types_in_vreq: HashSet<usize> = t
        .requirements
        .variable_requirements
        .iter()
        .flat_map(|(_, r)| anonymous_types_in(r))
        .collect();
    let sub_right_anonymous: HashBag<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .filter_map(|(_, a)| {
            if let Anonymous(n) = a {
                Some(*n)
            } else {
                None
            }
        })
        .collect();
    let sub_left_anonymous: HashBag<usize> = t
        .requirements
        .subtype_relation
        .iter()
        .filter_map(|(a, _)| {
            if let Anonymous(n) = a {
                Some(*n)
            } else {
                None
            }
        })
        .collect();
    for (a, b) in t.requirements.subtype_relation.clone() {
        match (a, b) {
            (Union(cs), b) => {
                for c in &cs {
                    t.requirements
                        .subtype_relation
                        .insert((c.clone(), b.clone()));
                }
                t.requirements
                    .subtype_relation
                    .remove(&(Union(cs), b));
            }
            (Fn(a1, r1), Fn(a2, r2)) => {
                t.requirements.subtype_relation.remove(&(
                    Fn(a1.clone(), r1.clone()),
                    Fn(a2.clone(), r2.clone()),
                ));
                t.requirements.subtype_relation.insert((*a2, *a1));
                t.requirements.subtype_relation.insert((*r1, *r2));
            }
            (a, b) if SubtypeOrd(&a) <= SubtypeOrd(&b) => {
                assert!(t
                    .requirements
                    .subtype_relation
                    .remove(&(a, b)));
            }
            (Anonymous(a), b)
                if !co_types.contains(&a)
                    && anonymous_types_in_sub_rel.contains(&a)
                        == 1
                    || anonymous_types_in_sub_rel.contains(&a)
                        == 2
                        && sub_left_anonymous.contains(&a) == 1
                        && sub_right_anonymous.contains(&a) == 1
                        && !anonymous_types_in_cons.contains(&a)
                        && !anonymous_types_in_vreq.contains(&a) =>
            {
                t = t.replace_num(a, &b);
                // break;
            }
            (b, Anonymous(a))
                if !contra_types.contains(&a)
                    && anonymous_types_in_sub_rel.contains(&a)
                        == 1 =>
            {
                t = t.replace_num(a, &b);
                // break;
            }
            (a, Union(cs)) if a.is_singleton() => {
                let new_cs: BTreeSet<Type> = cs
                    .clone()
                    .into_iter()
                    .filter(|c| !(c.is_singleton() && a != *c))
                    .collect();
                if new_cs.len() != cs.len() {
                    t.requirements
                        .subtype_relation
                        .insert((a.clone(), Union(new_cs)));
                    assert!(t
                        .requirements
                        .subtype_relation
                        .remove(&(a, Union(cs))));
                }
            }
            (Anonymous(a), Fn(_, _)) => {
                let new_fn_type = Fn(
                    Box::new(new_anonymous_type(
                        anonymous_type_count,
                    )),
                    Box::new(new_anonymous_type(
                        anonymous_type_count,
                    )),
                );
                t.requirements
                    .subtype_relation
                    .insert((Anonymous(a), new_fn_type.clone()));
                t.requirements
                    .subtype_relation
                    .insert((new_fn_type, Anonymous(a)));
            }
            // (Anonymous(a), b) if b.is_constructive() => {
            //     t.requirements
            //         .subtype_relation
            //         .insert((b, Anonymous(a)));
            // }
            _ => (),
        }
    }
    t
}

fn change_anonymous_num(
    mut t: Type,
    anonymous_type_count: &mut usize,
) -> Type {
    let anos = anonymous_types_in(&t);
    for a in anos {
        t = t
            .replace_num(a, &new_anonymous_type(anonymous_type_count))
    }
    t
}

#[allow(unused)]
fn possible_weakest(
    t: usize,
    subtype_relation: &BTreeSet<(Type, Type)>,
) -> Option<&Type> {
    let mut up = Vec::new();
    for (sub, sup) in subtype_relation {
        if *sub == Type::Anonymous(t) {
            up.push(sup);
        } else if sub.contains(t) {
            return None;
        }
    }
    if up.len() == 1 {
        Some(up[0])
    } else {
        unimplemented!()
    }
}

#[allow(unused)]
fn possible_strongest(
    t: usize,
    subtype_relation: &BTreeSet<(Type, Type)>,
) -> Option<&Type> {
    let mut down = Vec::new();
    for (sub, sup) in subtype_relation {
        if *sup == Type::Anonymous(t) {
            down.push(sub);
        } else if sup.contains(t) {
            return None;
        }
    }
    if down.len() == 1 {
        Some(down[0])
    } else {
        unimplemented!()
    }
}

fn new_anonymous_type(anonymous_type_count: &mut usize) -> Type {
    *anonymous_type_count += 1;
    Type::Anonymous(*anonymous_type_count - 1)
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
        Type::Anonymous(_) => Vec::new(),
    }
}

fn anonymous_types_in(t: &Type) -> Vec<usize> {
    match t {
        Type::Fn(a, r) => {
            [anonymous_types_in(a), anonymous_types_in(r)].concat()
        }
        Type::Normal(_, cs) => {
            cs.iter().map(|c| anonymous_types_in(c)).concat()
        }
        Type::Union(cs) => {
            cs.iter().map(|c| anonymous_types_in(c)).concat()
        }
        Type::Anonymous(n) => vec![*n],
    }
}

impl IncompleteType {
    fn replace_num(self, from: usize, to: &Type) -> Self {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation: subtype_relationship,
                },
        } = self;
        IncompleteType {
            constructor: constructor.replace_num(from, to),
            requirements: Requirements {
                variable_requirements: variable_requirements
                    .into_iter()
                    .map(|(name, t)| (name, t.replace_num(from, to)))
                    .collect(),
                subtype_relation: subtype_relationship
                    .into_iter()
                    .filter_map(|(a, b)| {
                        let a = a.replace_num(from, to);
                        let b = b.replace_num(from, to);
                        if a == b {
                            None
                        } else {
                            Some((a, b))
                        }
                    })
                    .collect(),
            },
        }
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

impl Type {
    fn replace_num(self, from: usize, to: &Type) -> Self {
        match self {
            Type::Fn(args, rtn) => Type::Fn(
                args.replace_num(from, to).into(),
                rtn.replace_num(from, to).into(),
            ),
            Type::Union(m) => Type::Union(
                m.into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect(),
            ),
            Type::Normal(name, cs) => Type::Normal(
                name,
                cs.into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect(),
            ),
            Type::Anonymous(n) => {
                if n == from {
                    to.clone()
                } else {
                    Type::Anonymous(n)
                }
            }
        }
    }

    fn is_singleton(&self) -> bool {
        match self {
            Type::Normal(_, cs) => {
                cs.iter().all(|c| c.is_singleton())
            }
            Type::Fn(a, b) => a.is_singleton() && b.is_singleton(),
            _ => false,
        }
    }

    fn contains(&self, variable_num: usize) -> bool {
        match self {
            Type::Normal(_, cs) => {
                cs.iter().any(|c| c.contains(variable_num))
            }
            Type::Fn(a, r) => {
                a.contains(variable_num) || r.contains(variable_num)
            }
            Type::Union(cs) => {
                cs.iter().any(|cs| cs.contains(variable_num))
            }
            Type::Anonymous(n) => *n == variable_num,
        }
    }
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
                "{}",
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
