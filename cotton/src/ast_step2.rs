pub mod decl_id;
pub mod ident_id;
pub mod types;

use self::types::TypeVariable;
use self::{
    decl_id::DeclId,
    ident_id::{new_ident_id, IdentId},
    types::{Type, TypeUnit},
};
use crate::{
    ast_step1,
    intrinsics::{
        IntrinsicConstructor, IntrinsicType, INTRINSIC_CONSTRUCTORS,
        INTRINSIC_TYPES,
    },
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::Display;
pub use types::TypeConstructor;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum ConstructorId<'a> {
    DeclId(DeclId, &'a str),
    Intrinsic(IntrinsicConstructor),
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub enum TypeId {
    DeclId(DeclId),
    Intrinsic(IntrinsicType),
}

/// # Difference between `ast_step1::Ast` and `ast_step2::Ast`
/// - The names of types and constructors are resolved.
/// - Local variable declarations are converted into lambdas and function calls.
#[derive(Debug, PartialEq, Clone)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub fields: Vec<TypeVariable>,
    pub decl_id: DeclId,
}

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default,
)]
pub struct SubtypeRelations<'a>(pub BTreeSet<(Type<'a>, Type<'a>)>);

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub enum PatternUnitForRestriction<'a> {
    I64,
    Str,
    Constructor {
        id: TypeId,
        name: &'a str,
        args: Vec<PatternUnitForRestriction<'a>>,
    },
    Binder(Type<'a>, DeclId),
}

pub type PatternForRestriction<'a> =
    Vec<PatternUnitForRestriction<'a>>;
pub type PatternRestrictions<'a> =
    Vec<(Type<'a>, Vec<PatternUnitForRestriction<'a>>)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IncompleteType<'a, T = Type<'a>>
where
    T: TypeConstructor<'a>,
{
    pub constructor: T,
    pub variable_requirements:
        Vec<(&'a str, Type<'a>, IdentId, TypeVariable)>,
    pub subtype_relations: SubtypeRelations<'a>,
    pub pattern_restrictions: PatternRestrictions<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_annotation: Option<IncompleteType<'a>>,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, TypeVariable);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident { name: &'a str, ident_id: IdentId },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    Do(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub expr: ExprWithType<'a>,
}

/// Represents a multi-case pattern which matches if any of the `PatternUnit` in it matches.
/// It should have at least one `PatternUnit`.
pub type Pattern<'a> = Vec<PatternUnit<'a>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternUnit<'a> {
    I64(&'a str),
    Str(&'a str),
    Constructor {
        id: ConstructorId<'a>,
        args: Vec<Pattern<'a>>,
    },
    Binder(&'a str, DeclId),
    Underscore,
    TypeRestriction(Pattern<'a>, Type<'a>),
}

impl<'a> From<ast_step1::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step1::Ast<'a>) -> Self {
        let data_decl: Vec<_> = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
                fields: (0..d.field_len)
                    .map(|_| TypeVariable::new())
                    .collect(),
                decl_id: DeclId::new(),
            })
            .collect();
        let data_decl_map: FxHashMap<&str, DeclId> =
            data_decl.iter().map(|d| (d.name, d.decl_id)).collect();
        let mut type_alias_map = TypeAliasMap(
            ast.type_alias_decl
                .into_iter()
                .map(|a| {
                    (a.name, (a.body, AliasComputation::NotUnaliased))
                })
                .collect(),
        );
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| {
                variable_decl(
                    d,
                    &data_decl_map,
                    &Default::default(),
                    &mut type_alias_map,
                )
            })
            .collect();
        let entry_point = variable_decl
            .iter()
            .find(|d| d.name == "main")
            .unwrap_or_else(|| panic!("entry point not found"))
            .decl_id;
        Self {
            variable_decl,
            data_decl,
            entry_point,
        }
    }
}

impl<'a> ConstructorId<'a> {
    pub fn name(&self) -> &'a str {
        match self {
            ConstructorId::DeclId(_, name) => name,
            ConstructorId::Intrinsic(c) => c.to_str(),
        }
    }
}

impl<'a> From<ConstructorId<'a>> for TypeId {
    fn from(c: ConstructorId<'a>) -> Self {
        match c {
            ConstructorId::DeclId(ident, _) => Self::DeclId(ident),
            ConstructorId::Intrinsic(i) => Self::Intrinsic(i.into()),
        }
    }
}

impl<'a> From<Type<'a>> for IncompleteType<'a> {
    fn from(t: Type<'a>) -> Self {
        Self {
            constructor: t,
            variable_requirements: Default::default(),
            subtype_relations: Default::default(),
            pattern_restrictions: Default::default(),
        }
    }
}

impl<'a> From<PatternUnit<'a>> for Pattern<'a> {
    fn from(p: PatternUnit<'a>) -> Self {
        vec![p]
    }
}

fn variable_decl<'a>(
    v: ast_step1::VariableDecl<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
) -> VariableDecl<'a> {
    let mut type_variable_names = type_variable_names.clone();
    VariableDecl {
        name: v.name,
        type_annotation: v.type_annotation.map(|(t, forall)| {
            type_variable_names.extend(
                forall
                    .type_variables
                    .into_iter()
                    .map(|s| (s, TypeVariable::new())),
            );
            type_to_type(
                t,
                data_decl_map,
                &type_variable_names,
                type_alias_map,
                SearchMode::Normal,
            )
            .into()
        }),
        value: expr(
            v.value,
            data_decl_map,
            &type_variable_names,
            type_alias_map,
        ),
        decl_id: DeclId::new(),
    }
}

fn expr<'a>(
    e: ast_step1::Expr<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
) -> ExprWithType<'a> {
    use Expr::*;
    let e = match e {
        ast_step1::Expr::Lambda(arms) => Lambda(
            arms.into_iter()
                .map(move |arm| {
                    fn_arm(
                        arm,
                        data_decl_map,
                        type_variable_names,
                        type_alias_map,
                    )
                })
                .collect(),
        ),
        ast_step1::Expr::Number(n) => Number(n),
        ast_step1::Expr::StrLiteral(s) => StrLiteral(s),
        ast_step1::Expr::Ident(name) => Ident {
            name,
            ident_id: new_ident_id(),
        },
        ast_step1::Expr::Decl(d) => {
            let d = variable_decl(
                *d,
                data_decl_map,
                type_variable_names,
                type_alias_map,
            );
            d.value.0
        }
        ast_step1::Expr::Call(f, a) => Call(
            Box::new(expr(
                *f,
                data_decl_map,
                type_variable_names,
                type_alias_map,
            )),
            Box::new(expr(
                *a,
                data_decl_map,
                type_variable_names,
                type_alias_map,
            )),
        ),
        ast_step1::Expr::Do(es) => {
            let mut new_es = Vec::new();
            for e in es.into_iter().rev() {
                new_es = add_expr_in_do(
                    e,
                    new_es,
                    data_decl_map,
                    type_variable_names,
                    type_alias_map,
                );
            }
            new_es.reverse();
            Do(new_es)
        }
    };
    (e, TypeVariable::new())
}

fn add_expr_in_do<'a>(
    e: ast_step1::Expr<'a>,
    mut es: Vec<ExprWithType<'a>>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
) -> Vec<ExprWithType<'a>> {
    match e {
        ast_step1::Expr::Decl(d) => {
            let d = variable_decl(
                *d,
                data_decl_map,
                type_variable_names,
                type_alias_map,
            );
            if es.is_empty() {
                vec![
                    (
                        Expr::Ident {
                            name: "()",
                            ident_id: new_ident_id(),
                        },
                        TypeVariable::new(),
                    ),
                    d.value,
                ]
            } else {
                es.reverse();
                let l = Expr::Lambda(vec![FnArm {
                    pattern: vec![PatternUnit::Binder(
                        d.name, d.decl_id,
                    )
                    .into()],
                    pattern_type: vec![None],
                    expr: (Expr::Do(es), TypeVariable::new()),
                }]);
                vec![(
                    Expr::Call(
                        Box::new((l, TypeVariable::new())),
                        Box::new(d.value),
                    ),
                    TypeVariable::new(),
                )]
            }
        }
        e => {
            es.push(expr(
                e,
                data_decl_map,
                type_variable_names,
                type_alias_map,
            ));
            es
        }
    }
}

fn fn_arm<'a>(
    arm: ast_step1::FnArm<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
) -> FnArm<'a> {
    FnArm {
        pattern: arm
            .pattern
            .into_iter()
            .map(|p| pattern(p, data_decl_map))
            .collect(),
        pattern_type: arm
            .pattern_type
            .into_iter()
            .map(|o| {
                o.map(|t| {
                    type_to_type(
                        t,
                        data_decl_map,
                        type_variable_names,
                        type_alias_map,
                        SearchMode::Normal,
                    )
                })
            })
            .collect(),
        expr: expr(
            arm.expr,
            data_decl_map,
            type_variable_names,
            type_alias_map,
        ),
    }
}

impl TypeId {
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> TypeId {
        if let Some(id) = data_decl_map.get(name) {
            TypeId::DeclId(*id)
        } else if let Some(i) = INTRINSIC_TYPES.get(name) {
            TypeId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

impl ConstructorId<'_> {
    fn get<'a>(
        name: &'a str,
        data_decl_map: &FxHashMap<&str, DeclId>,
    ) -> ConstructorId<'a> {
        if let Some(id) = data_decl_map.get(name) {
            ConstructorId::DeclId(*id, name)
        } else if let Some(i) = INTRINSIC_CONSTRUCTORS.get(name) {
            ConstructorId::Intrinsic(*i)
        } else {
            panic!("{:?} not fould", name)
        }
    }
}

fn pattern<'a>(
    p: ast_step1::Pattern<'a>,
    data_decl_map: &FxHashMap<&str, DeclId>,
) -> Pattern<'a> {
    use PatternUnit::*;
    match p {
        ast_step1::Pattern::Number(n) => I64(n),
        ast_step1::Pattern::StrLiteral(s) => Str(s),
        ast_step1::Pattern::Constructor { name, args } => {
            Constructor {
                id: ConstructorId::get(name, data_decl_map),
                args: args
                    .into_iter()
                    .map(|arg| pattern(arg, data_decl_map))
                    .collect(),
            }
        }
        ast_step1::Pattern::Binder(name) => {
            Binder(name, DeclId::new())
        }
        ast_step1::Pattern::Underscore => Underscore,
    }
    .into()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchMode {
    Normal,
    Alias,
    AliasSub,
}

pub fn type_to_type<'a>(
    t: ast_step1::Type<'a>,
    data_decl_map: &FxHashMap<&'a str, DeclId>,
    type_variable_names: &FxHashMap<&'a str, TypeVariable>,
    type_alias_map: &mut TypeAliasMap<'a>,
    search_type: SearchMode,
) -> Type<'a> {
    match t.name {
        "|" => t
            .args
            .into_iter()
            .flat_map(|a| {
                type_to_type(
                    a,
                    data_decl_map,
                    type_variable_names,
                    type_alias_map,
                    search_type,
                )
            })
            .collect(),
        "->" => TypeUnit::Fn(
            type_to_type(
                t.args[0].clone(),
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
            ),
            type_to_type(
                t.args[1].clone(),
                data_decl_map,
                type_variable_names,
                type_alias_map,
                search_type,
            ),
        )
        .into(),
        _ => {
            if let Some(n) = type_variable_names.get(t.name) {
                TypeUnit::Variable(*n).into()
            } else if let Some(i) = INTRINSIC_TYPES.get(&t.name) {
                TypeUnit::Normal {
                    name: t.name,
                    args: t
                        .args
                        .into_iter()
                        .map(|a| {
                            type_to_type(
                                a,
                                data_decl_map,
                                type_variable_names,
                                type_alias_map,
                                search_type,
                            )
                        })
                        .collect(),
                    id: TypeId::Intrinsic(*i),
                }
                .into()
            } else if let Some((mut unaliased, forall)) =
                type_alias_map.get(
                    t.name,
                    data_decl_map,
                    type_variable_names,
                    if search_type == SearchMode::Normal {
                        SearchMode::Alias
                    } else {
                        SearchMode::AliasSub
                    },
                )
            {
                for (from, to) in forall.0.into_iter().zip(t.args) {
                    unaliased = unaliased.replace_num(
                        from,
                        &type_to_type(
                            to,
                            data_decl_map,
                            type_variable_names,
                            type_alias_map,
                            search_type,
                        ),
                    );
                }
                unaliased
            } else {
                TypeUnit::Normal {
                    name: t.name,
                    args: t
                        .args
                        .into_iter()
                        .map(|a| {
                            type_to_type(
                                a,
                                data_decl_map,
                                type_variable_names,
                                type_alias_map,
                                search_type,
                            )
                        })
                        .collect(),
                    id: TypeId::get(t.name, data_decl_map),
                }
                .into()
            }
        }
    }
}

impl std::fmt::Display for ConstructorId<'_> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            ConstructorId::Intrinsic(a) => std::fmt::Debug::fmt(a, f),
            ConstructorId::DeclId(a, _) => a.fmt(f),
        }
    }
}

#[derive(Debug, Clone)]
enum AliasComputation<'a> {
    Unaliased(Type<'a>, Forall),
    NotUnaliased,
}

#[derive(Debug, Clone, Default)]
pub struct TypeAliasMap<'a>(
    FxHashMap<
        &'a str,
        (
            (ast_step1::Type<'a>, ast_step1::Forall<'a>),
            AliasComputation<'a>,
        ),
    >,
);

#[derive(Debug, Clone)]
struct Forall(Vec<TypeVariable>);

impl<'a> TypeAliasMap<'a> {
    fn get(
        &mut self,
        name: &'a str,
        data_decl_map: &FxHashMap<&'a str, DeclId>,
        type_variable_names: &FxHashMap<&'a str, TypeVariable>,
        search_type: SearchMode,
    ) -> Option<(Type<'a>, Forall)> {
        debug_assert_ne!(search_type, SearchMode::Normal);
        let alias = self.0.get(name)?;
        Some(match (&alias, search_type) {
            (
                (_, AliasComputation::Unaliased(t, forall)),
                SearchMode::Alias,
            ) => {
                let mut t = t.clone();
                let mut new_forall = Vec::new();
                for v in &forall.0 {
                    let new_v = TypeVariable::new();
                    t = t.replace_num(
                        *v,
                        &TypeUnit::Variable(new_v).into(),
                    );
                    new_forall.push(new_v);
                }
                (t, Forall(new_forall))
            }
            ((t, _), _) => {
                let mut type_variable_names: FxHashMap<
                    &'a str,
                    TypeVariable,
                > = type_variable_names
                    .clone()
                    .into_iter()
                    .map(|(s, v)| (s, v.increment_recursive_index()))
                    .collect();
                type_variable_names
                    .insert(name, TypeVariable::RecursiveIndex(0));
                let forall =
                    t.1.clone()
                        .type_variables
                        .into_iter()
                        .map(|s| {
                            let v = TypeVariable::new();
                            type_variable_names.insert(s, v);
                            v
                        })
                        .collect_vec();
                let new_t = type_to_type(
                    t.0.clone(),
                    data_decl_map,
                    &type_variable_names,
                    self,
                    search_type,
                );
                let new_t = if new_t
                    .all_type_variables()
                    .contains(&TypeVariable::RecursiveIndex(0))
                {
                    TypeUnit::RecursiveAlias { body: new_t }.into()
                } else {
                    new_t
                };
                if search_type == SearchMode::Alias {
                    self.0.get_mut(name).unwrap().1 =
                        AliasComputation::Unaliased(
                            new_t.clone(),
                            Forall(forall.clone()),
                        );
                }
                (decrement_index_outside(new_t), Forall(forall))
            }
        })
    }
}

fn decrement_index_outside(t: Type) -> Type {
    t.into_iter().map(decrement_index_outside_unit).collect()
}

fn decrement_index_outside_unit(t: TypeUnit) -> TypeUnit {
    match t {
        TypeUnit::Normal { name, args, id } => TypeUnit::Normal {
            name,
            args: args
                .into_iter()
                .map(decrement_index_outside)
                .collect(),
            id,
        },
        TypeUnit::Fn(a, b) => TypeUnit::Fn(
            decrement_index_outside(a),
            decrement_index_outside(b),
        ),
        TypeUnit::Variable(v)
            if v == TypeVariable::RecursiveIndex(1) =>
        {
            TypeUnit::Variable(TypeVariable::RecursiveIndex(0))
        }
        TypeUnit::Variable(v) => TypeUnit::Variable(v),
        TypeUnit::RecursiveAlias { body } => {
            TypeUnit::RecursiveAlias { body }
        }
    }
}

impl<'a> IntoIterator for SubtypeRelations<'a> {
    type Item = (Type<'a>, Type<'a>);
    type IntoIter =
        std::collections::btree_set::IntoIter<(Type<'a>, Type<'a>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'b SubtypeRelations<'a> {
    type Item = &'b (Type<'a>, Type<'a>);
    type IntoIter =
        std::collections::btree_set::Iter<'b, (Type<'a>, Type<'a>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> FromIterator<(Type<'a>, Type<'a>)> for SubtypeRelations<'a> {
    fn from_iter<T: IntoIterator<Item = (Type<'a>, Type<'a>)>>(
        iter: T,
    ) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a> SubtypeRelations<'a> {
    pub fn iter(
        &self,
    ) -> std::collections::btree_set::Iter<(Type<'a>, Type<'a>)> {
        self.0.iter()
    }

    pub fn insert(&mut self, value: (Type<'a>, Type<'a>)) -> bool {
        self.0.insert(value)
    }

    pub fn remove(&mut self, value: &(Type<'a>, Type<'a>)) -> bool {
        self.0.remove(value)
    }
}

impl<'a> Extend<(Type<'a>, Type<'a>)> for SubtypeRelations<'a> {
    fn extend<T: IntoIterator<Item = (Type<'a>, Type<'a>)>>(
        &mut self,
        iter: T,
    ) {
        self.0.extend(iter)
    }
}

impl<'a> Display for PatternUnitForRestriction<'a> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            PatternUnitForRestriction::I64 => write!(f, "I64Lit"),
            PatternUnitForRestriction::Str => write!(f, "StrLit"),
            PatternUnitForRestriction::Constructor {
                id: _,
                name,
                args,
            } => {
                write!(
                    f,
                    "{name}({})",
                    args.iter().map(|p| format!("{p}")).join(", ")
                )
            }
            PatternUnitForRestriction::Binder(b, decl_id) => {
                write!(f, "Bind({b}, id = {decl_id})")
            }
        }
    }
}

impl<'a> PatternUnitForRestriction<'a> {
    pub fn covariant_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str => Default::default(),
            PatternUnitForRestriction::Constructor {
                args,
                ..
            } => args
                .iter()
                .flat_map(PatternUnitForRestriction::covariant_type_variables)
                .collect(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.covariant_type_variables()
            }
        }
    }

    pub fn contravariant_type_variables(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str => Default::default(),
            PatternUnitForRestriction::Constructor {
                args,
                ..
            } => args
                .iter()
                .flat_map(PatternUnitForRestriction::contravariant_type_variables)
                .collect(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.contravariant_type_variables()
            }
        }
    }

    pub fn all_type_variables_vec(&self) -> Vec<TypeVariable> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str => Default::default(),
            PatternUnitForRestriction::Constructor {
                args, ..
            } => args
                .iter()
                .flat_map(
                    PatternUnitForRestriction::all_type_variables_vec,
                )
                .collect(),
            PatternUnitForRestriction::Binder(t, _) => {
                t.all_type_variables_vec()
            }
        }
    }

    pub fn all_type_variables(&self) -> FxHashSet<TypeVariable> {
        self.all_type_variables_vec().into_iter().collect()
    }

    pub fn decl_type_map(&self) -> Vec<(DeclId, &Type<'a>)> {
        match self {
            PatternUnitForRestriction::I64
            | PatternUnitForRestriction::Str => Default::default(),
            PatternUnitForRestriction::Constructor {
                args, ..
            } => {
                args.iter().flat_map(|p| p.decl_type_map()).collect()
            }
            PatternUnitForRestriction::Binder(t, decl_id) => {
                vec![(*decl_id, t)]
            }
        }
    }

    pub fn map_type<F>(self, f: F) -> Self
    where
        F: FnMut(Type<'a>) -> Type<'a>,
    {
        self.map_type_rec(f).0
    }

    fn map_type_rec<F>(self, mut f: F) -> (Self, F)
    where
        F: FnMut(Type<'a>) -> Type<'a>,
    {
        use PatternUnitForRestriction::*;
        match self {
            a @ (I64 | Str) => (a, f),
            Constructor { id, name, args } => (
                Constructor {
                    id,
                    name,
                    args: {
                        let mut new_args =
                            Vec::with_capacity(args.len());
                        for p in args {
                            let new_p: PatternUnitForRestriction;
                            (new_p, f) = p.map_type_rec(f);
                            new_args.push(new_p);
                        }
                        new_args
                    },
                },
                f,
            ),
            Binder(t, decl_id) => (Binder(f(t), decl_id), f),
        }
    }
}
