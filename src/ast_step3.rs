mod type_check;
pub mod type_util;

pub use self::type_check::VariableId;
use self::type_check::{
    type_check, ResolvedIdents, TypeVariableTracker,
};
use crate::ast_step2::{
    self,
    decl_id::DeclId,
    types::{Type, TypeMatchable, TypeVariable},
    DataDecl, IncompleteType, Pattern, TypeConstructor,
};
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;

/// # Difference between `ast_step2::Ast` and `ast_step3::Ast`
/// - The names of variables are resolved.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
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
    Ident {
        name: &'a str,
        variable_id: VariableId,
        type_args: Vec<(TypeVariable, Type<'a>)>,
    },
    Decl(Box<VariableDecl<'a>>),
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    Do(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub pattern_type: Vec<Option<Type<'a>>>,
    pub expr: ExprWithType<'a>,
}

impl<'a> From<ast_step2::Ast<'a>> for Ast<'a> {
    fn from(ast: ast_step2::Ast<'a>) -> Self {
        let (
            resolved_idents,
            types_of_decls,
            mut type_variable_tracker,
        ) = type_check(&ast);
        log::trace!("{:?}", resolved_idents);
        log::debug!(
            "type_variable_tracker: {}",
            type_variable_tracker
        );
        let variable_decl: Vec<_> = ast
            .variable_decl
            .into_iter()
            .map(move |d| {
                variable_decl(
                    d,
                    &resolved_idents,
                    &types_of_decls,
                    &mut type_variable_tracker,
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
        }
    }
}

fn variable_decl<'a>(
    d: ast_step2::VariableDecl<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> VariableDecl<'a> {
    let decl_type = types_of_decls.get(&d.decl_id).unwrap();
    assert_eq!(0, decl_type.variable_requirements.len());
    let type_ = IncompleteType {
        constructor: type_variable_tracker
            .normalize_type(decl_type.constructor.clone()),
        variable_requirements: Vec::new(),
        subtype_relation: decl_type
            .subtype_relation
            .iter()
            .map(|(a, b)| {
                (
                    type_variable_tracker.normalize_type(a.clone()),
                    type_variable_tracker.normalize_type(b.clone()),
                )
            })
            .collect(),
    };
    let value = expr(
        d.value,
        resolved_idents,
        types_of_decls,
        &type_.all_type_variables(),
        type_variable_tracker,
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
    type_variable_tracker: &mut TypeVariableTracker<'a>,
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
                        type_variable_tracker,
                    )
                })
                .collect(),
        ),
        ast_step2::Expr::Number(a) => Number(a),
        ast_step2::Expr::StrLiteral(a) => StrLiteral(a),
        ast_step2::Expr::Ident { name, ident_id } => {
            let (variable_id, type_args) = resolved_idents
                .get(&ident_id)
                .unwrap_or_else(|| {
                    panic!(
                        "{:?} not found in resolved_idents. \
                        name: {:?}",
                        ident_id, name
                    )
                })
                .clone();
            let type_args: Vec<_> = type_args
                .into_iter()
                .map(|(v, t)| {
                    let v = type_variable_tracker.find(v);
                    let v = match v.matchable() {
                        TypeMatchable::Variable(v) => v,
                        _ => panic!(),
                    };
                    let t = remove_free_type_variables(
                        type_variable_tracker.normalize_type(t),
                        fixed_variables,
                        type_variable_tracker,
                    );
                    (v, t)
                })
                .collect();
            log::debug!(
                "{} -- {} -- [{}]",
                name,
                ident_id,
                type_args.iter().format_with(", ", |(v, t), f| f(
                    &format!("({v} ~> {t})")
                ))
            );
            Ident {
                name,
                variable_id,
                type_args,
            }
        }
        ast_step2::Expr::Decl(a) => Decl(Box::new(variable_decl(
            *a,
            resolved_idents,
            types_of_decls,
            type_variable_tracker,
        ))),
        ast_step2::Expr::Call(f, a) => Call(
            expr(
                *f,
                resolved_idents,
                types_of_decls,
                fixed_variables,
                type_variable_tracker,
            )
            .into(),
            expr(
                *a,
                resolved_idents,
                types_of_decls,
                fixed_variables,
                type_variable_tracker,
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
                    type_variable_tracker,
                )
            })
            .collect()),
    };
    let t = remove_free_type_variables(
        type_variable_tracker.find(t),
        fixed_variables,
        type_variable_tracker,
    );
    (e, t)
}

fn fn_arm<'a>(
    arm: ast_step2::FnArm<'a>,
    resolved_idents: &ResolvedIdents<'a>,
    types_of_decls: &FxHashMap<DeclId, IncompleteType<'a>>,
    fixed_variables: &FxHashSet<TypeVariable>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> FnArm<'a> {
    let expr = expr(
        arm.expr,
        resolved_idents,
        types_of_decls,
        fixed_variables,
        type_variable_tracker,
    );
    FnArm {
        pattern: arm.pattern,
        pattern_type: arm.pattern_type,
        expr,
    }
}

fn remove_free_type_variables<'a>(
    t: Type<'a>,
    fixed_variables: &FxHashSet<TypeVariable>,
    type_variable_tracker: &mut TypeVariableTracker<'a>,
) -> Type<'a> {
    for v in t.all_type_variables() {
        if !fixed_variables.contains(&v) {
            type_variable_tracker
                .insert(v, TypeMatchable::Empty.into());
        }
    }
    type_variable_tracker.normalize_type(t)
}
