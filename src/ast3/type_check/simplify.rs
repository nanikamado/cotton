use crate::ast2::{
    types::{Type, TypeMatchable, TypeMatchableRef, TypeUnit},
    IncompleteType, Requirements, TypeConstructor,
};
use fxhash::FxHashSet;
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{collections::BTreeSet, fmt::Display, iter::Extend, vec};

pub fn simplify_type<'a, T: TypeConstructor<'a>>(
    mut t: IncompleteType<'a, T>,
) -> Option<IncompleteType<'a, T>> {
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
    Some(t)
}

fn _simplify_type<'a, T: TypeConstructor<'a>>(
    mut t: IncompleteType<'a, T>,
) -> Option<(IncompleteType<'a, T>, bool)> {
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
        let vs = t
            .type_variables_in_constructors_or_variable_requirements(
            );
        let st =
            possible_strongest(*a, &t.requirements.subtype_relation);
        let we =
            possible_weakest(*a, &t.requirements.subtype_relation);
        match (st, we) {
            (Some(st), Some(we)) if st == we || !vs.contains(a) => {
                t = t.replace_num_option(*a, &st)?;
            }
            (_, Some(we)) if we.len() == 0 => {
                t = t.replace_num_option(
                    *a,
                    &TypeMatchable::Empty.into(),
                )?;
            }
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

fn simplify_subtype_rel<'a>(
    sub: Type<'a>,
    sup: Type<'a>,
) -> Option<Vec<(Type<'a>, Type<'a>)>> {
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
        (
            Normal {
                name: n1,
                args: cs1,
                ..
            },
            Normal {
                name: n2,
                args: cs2,
                ..
            },
        ) => {
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
        (Fn(_, _), Normal { .. })
        | (Normal { .. }, Fn(_, _))
        | (Fn(_, _), Empty)
        | (Normal { .. }, Empty) => None,
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
        (
            Normal { name, args, id },
            RecursiveAlias { alias, body },
        ) => simplify_subtype_rel(
            Normal { name, args, id }.into(),
            unwrap_recursive_alias(alias, body),
        ),
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
        (Normal { name, args, id }, Union(u)) => {
            let new_u: Type = u
                .into_iter()
                .filter(|c| {
                    if let TypeUnit::Normal { name: c_name, .. } = c {
                        *c_name == name
                    } else {
                        true
                    }
                })
                .collect();
            Some(vec![(
                TypeUnit::Normal { name, args, id }.into(),
                new_u,
            )])
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

/// Change `Cons[List[a], a] | Nil` to `List[a]`
fn lift_recursive_alias<'a, T>(t: T) -> T
where
    T: TypeConstructor<'a>,
{
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

fn possible_weakest<'a>(
    t: usize,
    subtype_relation: &BTreeSet<(Type<'a>, Type<'a>)>,
) -> Option<Type<'a>> {
    let mut up = FxHashSet::default();
    for (sub, sup) in subtype_relation {
        if sup.contravariant_type_variables().contains(&t) {
            return None;
        } else if *sub == TypeUnit::Variable(t).into() {
            up.insert(sup);
        } else if sub.covariant_type_variables().contains(&t) {
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
                if let TypeMatchableRef::Normal { name, .. } =
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

fn possible_strongest<'a>(
    t: usize,
    subtype_relation: &BTreeSet<(Type<'a>, Type<'a>)>,
) -> Option<Type<'a>> {
    let mut down = Vec::new();
    for (sub, sup) in subtype_relation {
        if sub.contravariant_type_variables().contains(&t) {
            return None;
        } else if *sup == TypeUnit::Variable(t).into() {
            down.push(sub);
        } else if sup.covariant_type_variables().contains(&t) {
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

fn mk_contravariant_candidates<'a, T: TypeConstructor<'a>>(
    t: &IncompleteType<'a, T>,
) -> FxHashSet<usize> {
    let mut rst: Vec<usize> =
        t.constructor.contravariant_type_variables();
    for (_, v, _) in &t.requirements.variable_requirements {
        rst.append(&mut v.covariant_type_variables());
    }
    rst.into_iter().collect()
}

fn mk_covariant_candidates<'a, T: TypeConstructor<'a>>(
    t: &IncompleteType<'a, T>,
) -> FxHashSet<usize> {
    let mut rst: Vec<usize> =
        t.constructor.covariant_type_variables();
    for (_, v, _) in &t.requirements.variable_requirements {
        rst.append(&mut v.contravariant_type_variables());
    }
    rst.into_iter().collect()
}

impl<'a, T> IncompleteType<'a, T>
where
    T: TypeConstructor<'a>,
{
    pub fn replace_num_option(
        self,
        from: usize,
        to: &Type<'a>,
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
}

fn mk_graph<'a, 'b>(
    subtype_relationship: &'b BTreeSet<(Type<'a>, Type<'a>)>,
) -> DiGraphMap<&'b Type<'a>, ()> {
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

impl<'a, T: TypeConstructor<'a>> IncompleteType<'a, T> {
    fn type_variables_in_constructors_or_variable_requirements(
        &self,
    ) -> FxHashSet<usize> {
        let mut s = self.constructor.all_type_variables();
        for (_, t, _) in &self.requirements.variable_requirements {
            s.extend(t.all_type_variables())
        }
        s
    }
}

impl<'a, T: TypeConstructor<'a>> Display for IncompleteType<'a, T> {
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

impl Display for Requirements<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        for (a, b) in &self.subtype_relation {
            writeln!(f, "    {} < {},", a, b)?;
        }
        for (a, b, id) in &self.variable_requirements {
            writeln!(f, "  {:<3}  ?{} : {},", id, a, b)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast0, ast1, ast2,
        ast2::{IncompleteType, Requirements},
        ast3::{
            type_check::simplify::simplify_type,
            type_util::{
                construct_type, construct_type_with_variables,
            },
        },
        parse,
    };

    #[test]
    fn simplify1() {
        let ast: ast0::Ast = parse::parse(
            r#"data a /\ b
            infixl 3 /\
            main : () -> ()
            = fn | () => () --
            test : Num /\ Num ->
            ((Num /\ Num | Num /\ t1 | t2 /\ Num | t3 /\ t4) -> Num | String)
            -> Num | String forall t1, t2, t3, t4 --
            = ()
            "#,
        )
        .unwrap()
        .1;
        let ast: ast1::Ast = ast.into();
        let ast: ast2::Ast = ast.into();
        let req_t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let dot = construct_type_with_variables(
            "a -> (a -> b) -> b",
            &["a", "b"],
            &Default::default(),
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
            format!("{}", st),
            "Num -> {Num | String} forall\n--"
        );
    }
}
