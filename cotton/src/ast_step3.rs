mod type_check;
pub mod type_util;

pub use self::type_check::{
    type_check, ResolvedIdents, TypeVariableMap, VariableId,
    VariableRequirement,
};
use crate::ast_step2::ident_id::IdentId;
use crate::ast_step2::types::TypeUnit;
use crate::ast_step2::PatternUnit;
use crate::ast_step2::{
    self,
    decl_id::DeclId,
    types::{Type, TypeMatchable, TypeVariable},
    DataDecl, IncompleteType, Pattern, SubtypeRelations, TypeConstructor,
};
pub use crate::ast_step3::type_check::ResolvedIdent;
use fxhash::{FxHashMap, FxHashSet};

/// # Difference between `ast_step2::Ast` and `ast_step3::Ast`
/// - The names of variables are resolved.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
    pub resolved_idents: ResolvedIdents<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub type_: IncompleteType<'a>,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, Type<'a>);

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
    pub expr: ExprWithType<'a>,
}

impl<'a> From<ast_step2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step2::Ast<'a>) -> Self {
        let (resolved_idents, types_of_decls, mut subtype_relations, mut map) =
            type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        log::trace!("map : {}", map);
        log::debug!("subtype_relations: {}", subtype_relations);
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(|d| {
                variable_decl(
                    d,
                    &resolved_idents,
                    &types_of_decls,
                    &mut subtype_relations,
                    &mut map,
                )
            })
            .collect();
        for v in &variable_decl {
            log::debug!("type_ {} : {}", v.name, v.type_);
        }
        Self {
            variable_decl,
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
            resolved_idents,
        }
    }
}

fn variable_decl<'a>(
    d: ast_step2::VariableDecl<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> VariableDecl<'a> {
    let decl_type = types_of_decls.get(&d.decl_id).unwrap();
    assert_eq!(0, decl_type.variable_requirements.len());
    let type_ = IncompleteType {
        constructor: map.normalize_type(decl_type.constructor.clone()),
        variable_requirements: Vec::new(),
        subtype_relations: decl_type
            .subtype_relations
            .0
            .iter()
            .map(|(a, b)| {
                (map.normalize_type(a.clone()), map.normalize_type(b.clone()))
            })
            .collect(),
        pattern_restrictions: decl_type.pattern_restrictions.clone(),
        already_considered_relations: decl_type
            .already_considered_relations
            .clone(),
    };
    let value = expr(
        d.value,
        resolved_idents,
        types_of_decls,
        &type_.all_type_variables(),
        subtype_relations,
        map,
    );
    VariableDecl {
        name: d.name,
        type_,
        value,
        decl_id: d.decl_id,
    }
}

fn expr<'a>(
    (e, t): ast_step2::ExprWithType<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    fixed_variables: &FxHashSet<TypeVariable>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> ExprWithType<'a> {
    use Expr::*;
    let e = match e {
        ast_step2::Expr::Lambda(a) => Lambda(
            a.into_iter()
                .map(|arm| {
                    fn_arm(
                        arm,
                        resolved_idents,
                        types_of_decls,
                        fixed_variables,
                        subtype_relations,
                        map,
                    )
                })
                .collect(),
        ),
        ast_step2::Expr::Number(a) => Number(a),
        ast_step2::Expr::StrLiteral(a) => StrLiteral(a),
        ast_step2::Expr::Ident { name, ident_id } => Ident { name, ident_id },
        ast_step2::Expr::Call(f, a) => Call(
            expr(
                *f,
                resolved_idents,
                types_of_decls,
                fixed_variables,
                subtype_relations,
                map,
            )
            .into(),
            expr(
                *a,
                resolved_idents,
                types_of_decls,
                fixed_variables,
                subtype_relations,
                map,
            )
            .into(),
        ),
        ast_step2::Expr::Do(es) => Do(es
            .into_iter()
            .map(|et| {
                expr(
                    et,
                    resolved_idents,
                    types_of_decls,
                    fixed_variables,
                    subtype_relations,
                    map,
                )
            })
            .collect()),
    };
    let t = remove_free_type_variables(
        map.find(t),
        fixed_variables,
        subtype_relations,
        map,
    );
    (e, lift_recursive_alias(t))
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
        let (t, updated) = t
            .replace_type_union_with_update_flag(&body, &TypeUnit::Variable(v));
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

fn fn_arm<'a>(
    arm: ast_step2::FnArm<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    fixed_variables: &FxHashSet<TypeVariable>,
    subtype_relations: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> FnArm<'a> {
    let expr = expr(
        arm.expr,
        resolved_idents,
        types_of_decls,
        fixed_variables,
        subtype_relations,
        map,
    );
    FnArm {
        pattern: normalize_types_in_pattern(arm.pattern, map),
        expr,
    }
}

fn normalize_types_in_pattern<'a>(
    pattern: Vec<Pattern<'a>>,
    map: &mut TypeVariableMap<'a>,
) -> Vec<Pattern<'a>> {
    pattern
        .into_iter()
        .map(|p| {
            p.into_iter()
                .map(|p| normalize_types_in_pattern_unit(p, map))
                .collect()
        })
        .collect()
}

fn normalize_types_in_pattern_unit<'a>(
    pattern: PatternUnit<'a>,
    map: &mut TypeVariableMap<'a>,
) -> PatternUnit<'a> {
    match pattern {
        PatternUnit::Binder(name, ident_id, t) => {
            PatternUnit::Binder(name, ident_id, map.normalize_type(t))
        }
        p => p,
    }
}

fn remove_free_type_variables<'a>(
    t: Type<'a>,
    fixed_variables: &FxHashSet<TypeVariable>,
    subtype_relatoins: &mut SubtypeRelations<'a>,
    map: &mut TypeVariableMap<'a>,
) -> Type<'a> {
    for v in t.all_type_variables() {
        if !fixed_variables.contains(&v) {
            map.insert(subtype_relatoins, v, TypeMatchable::Empty.into());
        }
    }
    map.normalize_type(t)
}
