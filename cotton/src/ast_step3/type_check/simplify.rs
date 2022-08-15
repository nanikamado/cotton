use crate::ast_step2::{
    self,
    ident_id::IdentId,
    types::{
        Type, TypeMatchable, TypeMatchableRef, TypeUnit, TypeVariable,
    },
    TypeConstructor,
};
use fxhash::FxHashSet;
use hashbag::HashBag;
use itertools::Itertools;
use petgraph::{self, algo::tarjan_scc, graphmap::DiGraphMap};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
    iter::Extend,
    vec,
};

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
)]
pub struct IncompleteType<'a, T = Type<'a>>
where
    T: TypeConstructor<'a>,
{
    pub constructor: T,
    pub variable_requirements: Vec<(&'a str, Type<'a>, IdentId)>,
    pub type_variable_tracker: TypeVariableTracker<'a>,
}

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
)]
pub struct TypeVariableMap<'a>(BTreeMap<TypeVariable, Type<'a>>);

impl<'a> TypeVariableMap<'a> {
    pub fn find(&mut self, key: TypeVariable) -> Type<'a> {
        if let Some(t) = self.0.get(&key).cloned() {
            let t_new = self.normalize_type(t.clone());
            if t_new == t {
                t
            } else {
                let t_new = lift_recursive_alias(t_new);
                self.0.insert(key, t_new.clone());
                t_new
            }
        } else {
            TypeUnit::Variable(key).into()
        }
    }

    pub fn normalize_type(&mut self, t: Type<'a>) -> Type<'a> {
        t.into_iter()
            .flat_map(|tu| match tu {
                TypeUnit::Fn(arg, rtn) => TypeUnit::Fn(
                    self.normalize_type(arg),
                    self.normalize_type(rtn),
                )
                .into(),
                TypeUnit::Variable(v) => self.find(v),
                TypeUnit::RecursiveAlias { alias, body } => {
                    let body = self.normalize_type(body);
                    match body.matchable() {
                        TypeMatchable::RecursiveAlias {
                            alias: alias_inner,
                            body: body_inner,
                        } => body_inner.replace_num(
                            alias,
                            &TypeUnit::Variable(alias_inner).into(),
                        ),
                        body => TypeUnit::RecursiveAlias {
                            alias,
                            body: body.into(),
                        }
                        .into(),
                    }
                }
                TypeUnit::Normal { name, args, id } => {
                    if args.is_empty() {
                        TypeUnit::Normal { name, args, id }.into()
                    } else {
                        args.into_iter()
                            .map(|t| {
                                self.normalize_type(t).partition()
                            })
                            .multi_cartesian_product()
                            .map(|args| TypeUnit::Normal {
                                name,
                                args,
                                id,
                            })
                            .collect()
                    }
                }
            })
            .collect()
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
)]
pub struct TypeVariableTracker<'a> {
    pub map: TypeVariableMap<'a>,
    pub subtype_relation: BTreeSet<(Type<'a>, Type<'a>)>,
}

impl<'a> TypeVariableTracker<'a> {
    pub fn insert(&mut self, k: TypeVariable, v: Type<'a>) {
        let key = self.find(k);
        let value = self.normalize_type(v.clone());
        log::debug!(
            "{k} {} ----> {v} {}",
            match key.matchable_ref() {
                TypeMatchableRef::Variable(key) if k == key =>
                    "".to_string(),
                _ => format!("({})", key),
            },
            if v == value {
                "".to_string()
            } else {
                format!("({})", value)
            }
        );
        if key == value {
            return;
        }
        use TypeMatchableRef::*;
        let (key, value) =
            match (key.matchable_ref(), value.matchable_ref()) {
                (Variable(key), Variable(value)) => {
                    if value < key {
                        (value, TypeUnit::Variable(key).into())
                    } else {
                        (key, TypeUnit::Variable(value).into())
                    }
                }
                (Variable(key), _)
                    if !value.all_type_variables().contains(&key) =>
                {
                    (key, value)
                }
                (_, Variable(value))
                    if !key.all_type_variables().contains(&value) =>
                {
                    (value, key)
                }
                (Variable(_), _) | (_, Variable(_)) => {
                    panic!("recursion is not allowed.",)
                }
                _ => {
                    self.add_subtype_rel(key.clone(), value.clone());
                    self.add_subtype_rel(value, key);
                    return;
                }
            };
        if let Some(old) = self.map.0.get(&key) {
            log::error!(
                "{key} is already pointing to {old}. ignored"
            );
        } else {
            self.map.0.insert(key, value);
        }
    }

    pub fn find(&mut self, key: TypeVariable) -> Type<'a> {
        self.map.find(key)
    }

    pub fn normalize_type(&mut self, t: Type<'a>) -> Type<'a> {
        self.map.normalize_type(t)
    }

    pub fn merge(mut self, other: Self) -> Self {
        for (v, t) in other.map.0 {
            self.insert(v, t);
        }
        self.add_subtype_rels(other.subtype_relation);
        self
    }

    pub fn possible_strongest(
        &mut self,
        t: TypeVariable,
    ) -> Option<Type<'a>> {
        let t = self.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_strongest(v, &self.subtype_relation)
        } else {
            Some(t)
        }
    }

    pub fn possible_weakest(
        &mut self,
        t: TypeVariable,
    ) -> Option<Type<'a>> {
        let t = self.find(t);
        if let TypeMatchableRef::Variable(v) = t.matchable_ref() {
            possible_weakest(v, &self.subtype_relation)
        } else {
            Some(t)
        }
    }

    pub fn type_variables_in_sub_rel<
        T: FromIterator<TypeVariable>,
    >(
        &self,
    ) -> T {
        self.subtype_relation
            .iter()
            .flat_map(|(a, b)| {
                a.all_type_variables()
                    .into_iter()
                    .chain(b.all_type_variables())
            })
            .collect()
    }

    pub fn normalize(mut self) -> Option<Self> {
        self = self.normalize_subtype_rel()?;
        let eqs = find_eq_types(&self.subtype_relation);
        let eqs_is_empty = eqs.is_empty();
        for (from, to) in eqs {
            self.insert(from, to);
        }
        if eqs_is_empty {
            Some(self)
        } else {
            self.normalize()
        }
    }

    fn normalize_subtype_rel(mut self) -> Option<Self> {
        self.subtype_relation = self
            .subtype_relation
            .into_iter()
            .map(|(a, b)| {
                simplify_subtype_rel(
                    self.map.normalize_type(a),
                    self.map.normalize_type(b),
                )
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect();
        Some(self)
    }

    pub fn add_subtype_rel(&mut self, sub: Type<'a>, sup: Type<'a>) {
        self.subtype_relation.insert((sub, sup));
    }

    pub fn add_subtype_rels<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (Type<'a>, Type<'a>)>,
    {
        self.subtype_relation.extend(iter)
    }
}

impl<'a, T: TypeConstructor<'a>>
    From<ast_step2::IncompleteType<'a, T>> for IncompleteType<'a, T>
{
    fn from(t: ast_step2::IncompleteType<'a, T>) -> Self {
        let ast_step2::IncompleteType {
            constructor,
            variable_requirements,
            subtype_relation,
        } = t;
        IncompleteType {
            constructor,
            variable_requirements,
            type_variable_tracker: TypeVariableTracker {
                map: Default::default(),
                subtype_relation,
            },
        }
    }
}

impl<'a> From<Type<'a>> for IncompleteType<'a> {
    fn from(t: Type<'a>) -> Self {
        Self {
            constructor: t,
            ..Default::default()
        }
    }
}

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
    let hash_before_simplify = fxhash::hash(&t);
    t = t.normalize()?;
    log::trace!("t = {}", t);
    t.constructor = lift_recursive_alias(t.constructor);
    for cov in mk_covariant_candidates(&t) {
        if !mk_contravariant_candidates(&t).contains(&cov) {
            if let Some(s) =
                t.type_variable_tracker.possible_strongest(cov)
            {
                if s.len() == 0 {
                    log::trace!("t{{0.5}} = {}", t);
                }
                t = t.replace_num_option(cov, &s)?;
                t = t.normalize()?;
                break;
            }
        }
    }
    log::trace!("t{{1}} = {}", t);
    for cont in mk_contravariant_candidates(&t) {
        if !mk_covariant_candidates(&t).contains(&cont) {
            if let Some(s) =
                t.type_variable_tracker.possible_weakest(cont)
            {
                t = t.replace_num_option(cont, &s)?;
                t = t.normalize()?;
                break;
            }
        }
    }
    log::trace!("t' = {}", t);
    let type_variables_in_sub_rel: FxHashSet<TypeVariable> =
        t.type_variable_tracker.type_variables_in_sub_rel();
    for a in &type_variables_in_sub_rel {
        let vs = t
            .type_variables_in_constructors_or_variable_requirements(
            );
        let st = t.type_variable_tracker.possible_strongest(*a);
        let we = t.type_variable_tracker.possible_weakest(*a);
        match (st, we) {
            (Some(st), Some(we)) if st == we || !vs.contains(a) => {
                if st.len() == 0 {
                    log::debug!("t'{{1}} = {t}");
                }
                t = t.replace_num_option(*a, &st)?;
                t = t.normalize()?;
                break;
            }
            (_, Some(we)) if we.len() == 0 => {
                t = t.replace_num_option(
                    *a,
                    &TypeMatchable::Empty.into(),
                )?;
                t = t.normalize()?;
                break;
            }
            _ => (),
        }
    }
    log::trace!("t'' = {}", t);
    let covariant_candidates = mk_covariant_candidates(&t);
    let contravariant_candidates = mk_contravariant_candidates(&t);
    let type_variables_in_sub_rel: HashBag<TypeVariable> =
        t.type_variable_tracker.type_variables_in_sub_rel();
    for (v, count) in type_variables_in_sub_rel {
        if count == 1
            && !covariant_candidates.contains(&v)
            && !contravariant_candidates.contains(&v)
        {
            if let Some(new_t) =
                t.type_variable_tracker.possible_strongest(v)
            {
                t = t.replace_num_option(v, &new_t).unwrap();
                t = t.normalize()?;
            }
        }
    }
    let updated = fxhash::hash(&t) != hash_before_simplify;
    Some((t, updated))
}

fn find_eq_types<'a>(
    subtype_rel: &BTreeSet<(Type<'a>, Type<'a>)>,
) -> Vec<(TypeVariable, Type<'a>)> {
    use TypeUnit::*;
    let g = mk_graph(subtype_rel);
    let eq_types = tarjan_scc(&g);
    let mut r = Vec::new();
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
                r.push((*a, Variable(eq_variable[0]).into()));
            }
        } else {
            for a in eq_variable {
                r.push((a, eq_cons[0].clone()));
            }
        }
    }
    r
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
        (t @ Normal { .. }, Union(tus)) => {
            let t: Type = t.into();
            let new_tus = tus
                .clone()
                .into_iter()
                .filter(|tu| {
                    simplify_subtype_rel(t.clone(), tu.clone().into())
                        .is_some()
                })
                .collect();
            if tus == new_tus {
                Some(vec![(t, tus)])
            } else {
                Some(simplify_subtype_rel(t.clone(), new_tus)?)
            }
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

fn unwrap_recursive_alias(alias: TypeVariable, body: Type) -> Type {
    body.clone().replace_num(
        alias,
        &(TypeUnit::RecursiveAlias { alias, body }).into(),
    )
}

fn possible_weakest<'a>(
    t: TypeVariable,
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
            let v = TypeVariable::new();
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
    t: TypeVariable,
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
        let v = TypeVariable::new();
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
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> =
        t.constructor.contravariant_type_variables();
    for (_, v, _) in &t.variable_requirements {
        rst.append(&mut v.covariant_type_variables());
    }
    rst.into_iter().collect()
}

fn mk_covariant_candidates<'a, T: TypeConstructor<'a>>(
    t: &IncompleteType<'a, T>,
) -> FxHashSet<TypeVariable> {
    let mut rst: Vec<TypeVariable> =
        t.constructor.covariant_type_variables();
    for (_, v, _) in &t.variable_requirements {
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
        from: TypeVariable,
        to: &Type<'a>,
    ) -> Option<Self> {
        let IncompleteType {
            constructor,
            variable_requirements,
            mut type_variable_tracker,
        } = self;
        type_variable_tracker.insert(from, to.clone());
        Some(IncompleteType {
            constructor: constructor.replace_num(from, to),
            variable_requirements: variable_requirements
                .into_iter()
                .map(|(name, t, id)| {
                    (name, t.replace_num(from, to), id)
                })
                .collect(),
            type_variable_tracker,
        })
    }

    pub fn destruct(
        self,
    ) -> (ast_step2::IncompleteType<'a, T>, TypeVariableTracker<'a>)
    {
        (
            ast_step2::IncompleteType {
                constructor: self.constructor,
                variable_requirements: self.variable_requirements,
                subtype_relation: self
                    .type_variable_tracker
                    .subtype_relation
                    .clone(),
            },
            self.type_variable_tracker,
        )
    }

    fn normalize(mut self) -> Option<Self> {
        self.type_variable_tracker =
            self.type_variable_tracker.normalize()?;
        Some(Self {
            constructor: self.constructor.map_type(|t| {
                self.type_variable_tracker.normalize_type(t)
            }),
            variable_requirements: self
                .variable_requirements
                .into_iter()
                .map(|(name, t, id)| {
                    (
                        name,
                        self.type_variable_tracker.normalize_type(t),
                        id,
                    )
                })
                .collect(),
            type_variable_tracker: self.type_variable_tracker,
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
    let zero = TypeVariable::new();
    let one = TypeVariable::new();
    assert_eq!(
        Variable(zero).replace_num(zero, &Variable(one).into()),
        Variable(one).into()
    );
}

#[test]
fn replace_type_test1() {
    use TypeUnit::*;
    let zero = TypeVariable::new();
    let one = TypeVariable::new();
    let two = TypeVariable::new();
    assert_eq!(
        Fn(Variable(zero).into(), Variable(two).into())
            .replace_num(zero, &Variable(one).into()),
        Fn(Variable(one).into(), Variable(two).into()).into()
    );
}

impl<'a, T: TypeConstructor<'a>> IncompleteType<'a, T> {
    fn type_variables_in_constructors_or_variable_requirements(
        &self,
    ) -> FxHashSet<TypeVariable> {
        let mut s = self.constructor.all_type_variables();
        for (_, t, _) in &self.variable_requirements {
            s.extend(t.all_type_variables())
        }
        s
    }
}

impl<'a, T: TypeConstructor<'a>> Display
    for ast_step2::IncompleteType<'a, T>
{
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "{} forall", self.constructor)?;
        for (a, b) in &self.subtype_relation {
            writeln!(f, "    {} < {},", a, b)?;
        }
        for (a, b, id) in &self.variable_requirements {
            writeln!(f, "  {:<3}  ?{} : {},", id, a, b)?;
        }
        write!(f, "--")?;
        Ok(())
    }
}

impl<'a, T: TypeConstructor<'a>> Display for IncompleteType<'a, T> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "{} forall", self.constructor)?;
        for (a, b, id) in &self.variable_requirements {
            writeln!(f, "  {:<3}  ?{} : {},", id, a, b)?;
        }
        writeln!(f, "--")?;
        write!(f, "{}", self.type_variable_tracker)?;
        Ok(())
    }
}

impl<'a> Display for TypeVariableTracker<'a> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        for (a, b) in &self.subtype_relation {
            writeln!(f, "    {} < {},", a, b)?;
        }
        write!(
            f,
            "[{}]",
            self.map
                .0
                .iter()
                .map(|(v, t)| format!("{} : {}", v, t))
                .join(", ")
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast_step1, ast_step2,
        ast_step2::{types::Type, IncompleteType},
        ast_step3::type_check::{
            simplify::{simplify_subtype_rel, simplify_type},
            TypeVariableTracker,
        },
    };

    #[test]
    fn simplify1() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> ()
        = | () => ()
        test : I64 /\ I64 ->
        ((I64 /\ I64 | I64 /\ t1 | t2 /\ I64 | t3 /\ t4) -> I64 | String)
        -> I64 | String forall {t1, t2, t3, t4}
        = ()
        dot : a -> (a -> b) -> b forall {a, b} = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
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
        let dot = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "dot")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t = IncompleteType {
            constructor: Type::from_str("I64").arrow(
                Type::from_str("I64").union(Type::from_str("String")),
            ),
            variable_requirements: Vec::new(),
            subtype_relation: vec![(dot, req_t)]
                .into_iter()
                .collect(),
        };
        let (st, _tracker) =
            simplify_type(t.into()).unwrap().destruct();
        assert_eq!(
            format!("{}", st),
            "I64 -> {I64 | String} forall\n--"
        );
    }

    #[test]
    fn simplify2() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        test : (True | False) /\ (True | False)
        = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let mut tracker = TypeVariableTracker::default();
        let t = tracker.normalize_type(t);
        assert_eq!(
            format!("{}", t),
            r"{/\(False, False) | /\(False, True) | /\(True, False) | /\(True, True)}"
        );
    }

    #[test]
    fn simplify3() {
        let src = r#"data a /\ b
        infixl 3 /\
        main : () -> () =
            | () => ()
        test1 : (False /\ False /\ False) = ()
        test2 : (True /\ a /\ b) |
            (c /\ True /\ d) |
            (e /\ f /\ True) forall {a,b,c,d,e,f} = ()
        "#;
        let ast = parse::parse(src);
        let ast: ast_step1::Ast = (&ast).into();
        let ast: ast_step2::Ast = ast.into();
        let t1 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test1")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t2 = ast
            .variable_decl
            .iter()
            .find(|d| d.name == "test2")
            .unwrap()
            .type_annotation
            .clone()
            .unwrap()
            .constructor
            .clone();
        let t = simplify_subtype_rel(t1.clone(), t2.clone());
        assert_eq!(format!("{:?}", t), "None");
    }
}
