mod type_check;
pub mod type_util;

pub use self::type_check::{
    simplify_subtype_rel, GlobalVariableType, LocalVariableType, ResolvedIdent,
    TypeVariableMap, VariableId, VariableRequirement,
};
use self::type_check::{type_check, TypeCheckResult};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Path;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::imports::Imports;
use crate::ast_step2::types::{Type, TypeConstructor, TypeUnit, TypeVariable};
use crate::ast_step2::{self, ApplyPattern, PatternUnit};
use crate::errors::CompileError;
use fxhash::FxHashMap;

/// Difference between `ast_step2::Ast` and `ast_step3::Ast`:
/// - The names of variables are resolved.
/// - Implicit parameters are converted to explicit parameters.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: Option<DeclId>,
    pub types_of_global_decls: FxHashMap<VariableId, GlobalVariableType>,
    pub types_of_local_decls: FxHashMap<VariableId, LocalVariableType>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: Path,
    pub value: ExprWithType<'a>,
    pub decl_id: DeclId,
}

pub type ExprWithType<'a> = (Expr<'a>, Type);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
    Lambda(Vec<FnArm<'a>>),
    Number(&'a str),
    StrLiteral(&'a str),
    Ident {
        name: String,
        variable_id: VariableId,
    },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

pub type Pattern<'a> = ast_step2::Pattern<'a, Type, Expr<'a>>;

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a>>,
    pub expr: ExprWithType<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Path,
    pub field_len: usize,
    pub decl_id: DeclId,
}

impl<'a> Ast<'a> {
    pub fn from(
        ast: ast_step2::Ast<'a>,
        token_map: &mut TokenMap,
        imports: &mut Imports,
    ) -> Result<(Self, FxHashMap<IdentId, ResolvedIdent>), CompileError> {
        let TypeCheckResult {
            resolved_idents,
            global_variable_types,
            mut local_variable_types,
            type_variable_map: mut map,
        } = type_check(&ast, token_map, imports)?;
        let variable_decl = variable_decl(
            ast.variable_decl,
            &resolved_idents,
            &mut map,
            &mut local_variable_types,
        );
        for v in &variable_decl {
            log::debug!(
                "type_ {} : {}",
                v.name,
                global_variable_types[&VariableId::Global(v.decl_id)].t
            );
        }
        let data_decl = ast
            .data_decl
            .into_iter()
            .map(|d| DataDecl {
                name: d.name,
                field_len: d.fields.len(),
                decl_id: d.decl_id,
            })
            .collect();
        Ok((
            Self {
                variable_decl,
                data_decl,
                entry_point: ast.entry_point,
                types_of_global_decls: global_variable_types,
                types_of_local_decls: local_variable_types,
            },
            resolved_idents,
        ))
    }
}

fn variable_decl<'a>(
    variable_decls: Vec<ast_step2::VariableDecl<'a>>,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
    types_of_decls: &mut FxHashMap<VariableId, LocalVariableType>,
) -> Vec<VariableDecl<'a>> {
    variable_decls
        .into_iter()
        .map(|d| {
            let (mut value, mut value_t) = expr(d.value, resolved_idents, map);
            for (name, t, decl_id) in d
                .type_annotation
                .into_iter()
                .flat_map(|ann| ann.implicit_parameters)
                .rev()
            {
                types_of_decls.insert(
                    VariableId::Local(decl_id),
                    LocalVariableType {
                        t: t.clone(),
                        toplevel: d.decl_id,
                    },
                );
                value = Expr::Lambda(vec![FnArm {
                    pattern: vec![ast_step2::Pattern(vec![
                        PatternUnit::Binder(name, decl_id, t.clone()),
                    ])],
                    expr: (value, value_t.clone()),
                }]);
                value_t = TypeUnit::Fn(t, value_t).into();
            }
            let value = (value, value_t);
            VariableDecl {
                name: d.name,
                value,
                decl_id: d.decl_id,
            }
        })
        .collect()
}

fn expr<'a>(
    (e, t, _): ast_step2::ExprWithTypeAndSpan<'a, TypeVariable>,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
) -> ExprWithType<'a> {
    let e = match e {
        ast_step2::Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter()
                .map(|a| {
                    let e = expr(a.expr, resolved_idents, map);
                    FnArm {
                        pattern: a
                            .pattern
                            .into_iter()
                            .map(|(p, _span)| {
                                normalize_types_in_pattern(
                                    p,
                                    resolved_idents,
                                    map,
                                )
                            })
                            .collect(),
                        expr: e,
                    }
                })
                .collect(),
        ),
        ast_step2::Expr::Number(a) => Expr::Number(a),
        ast_step2::Expr::StrLiteral(a) => Expr::StrLiteral(a),
        ast_step2::Expr::Ident { name, ident_id } => {
            let resolved_item = resolved_idents[&ident_id].clone();
            get_expr_from_resolved_ident(
                name.path.last().unwrap().0.to_string(),
                &resolved_item,
                map.find(t),
                resolved_idents,
            )
        }
        ast_step2::Expr::ResolvedIdent {
            variable_id: variable_id @ VariableId::Local(_),
            ..
        } => Expr::Ident {
            name: "unique".to_string(),
            variable_id,
        },
        ast_step2::Expr::ResolvedIdent {
            variable_id, name, ..
        } => Expr::Ident {
            name: name.unwrap().to_string(),
            variable_id,
        },
        ast_step2::Expr::Call(f, a) => Expr::Call(
            expr(*f, resolved_idents, map).into(),
            expr(*a, resolved_idents, map).into(),
        ),
        ast_step2::Expr::Do(es) => Expr::DoBlock(
            es.into_iter()
                .map(|e| expr(e, resolved_idents, map))
                .collect(),
        ),
        ast_step2::Expr::TypeAnnotation(v, _) => {
            return expr(*v, resolved_idents, map)
        }
    };
    (e, lift_recursive_alias(map.find(t)))
}

fn get_expr_from_resolved_ident(
    name: String,
    resolved_ident: &ResolvedIdent,
    t: Type,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
) -> Expr<'static> {
    let mut value = Expr::Ident {
        name,
        variable_id: resolved_ident.variable_id,
    };
    let mut ts = Vec::new();
    let mut fn_t = t;
    for (_, implicit_arg_t, _) in resolved_ident.implicit_args.iter().rev() {
        fn_t = TypeUnit::Fn(implicit_arg_t.clone(), fn_t).into();
        ts.push(fn_t.clone());
    }
    for ((name, implicit_arg_t, resolved_ident), fn_t) in resolved_ident
        .implicit_args
        .iter()
        .zip(ts.into_iter().rev())
    {
        value = Expr::Call(
            Box::new((value, fn_t)),
            Box::new((
                get_expr_from_resolved_ident(
                    name.to_string(),
                    &resolved_idents[resolved_ident],
                    implicit_arg_t.clone(),
                    resolved_idents,
                ),
                implicit_arg_t.clone(),
            )),
        );
    }
    value
}

/// Change `Cons[List[a], a] | Nil` to `List[a]`
fn lift_recursive_alias<T>(t: T) -> T
where
    T: TypeConstructor,
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

fn normalize_types_in_pattern<'a>(
    pattern: ast_step2::Pattern<'a, TypeVariable>,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
) -> Pattern<'a> {
    ast_step2::Pattern(
        pattern
            .0
            .into_iter()
            .map(|p| normalize_types_in_pattern_unit(p, resolved_idents, map))
            .collect(),
    )
}

fn normalize_types_in_pattern_unit<'a>(
    pattern: PatternUnit<'a, TypeVariable>,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
) -> PatternUnit<'a, Type, Expr<'a>> {
    match pattern {
        PatternUnit::Binder(name, ident_id, t) => {
            PatternUnit::Binder(name, ident_id, map.find(t))
        }
        PatternUnit::ResolvedBinder(decl_id, t) => {
            PatternUnit::Binder("unique".to_string(), decl_id, map.find(t))
        }
        PatternUnit::I64(a) => PatternUnit::I64(a),
        PatternUnit::Str(a) => PatternUnit::Str(a),
        PatternUnit::Constructor { name, id, args } => {
            PatternUnit::Constructor {
                name,
                id,
                args: args
                    .into_iter()
                    .map(|(p, span)| {
                        (
                            normalize_types_in_pattern(p, resolved_idents, map),
                            span,
                        )
                    })
                    .collect(),
            }
        }
        PatternUnit::Underscore => PatternUnit::Underscore,
        PatternUnit::TypeRestriction(p, t) => PatternUnit::TypeRestriction(
            normalize_types_in_pattern(p, resolved_idents, map),
            t,
        ),
        PatternUnit::Apply(pre_pattern, applications) => PatternUnit::Apply(
            Box::new(normalize_types_in_pattern(
                *pre_pattern,
                resolved_idents,
                map,
            )),
            applications
                .into_iter()
                .map(|a| ApplyPattern {
                    function: expr(a.function, resolved_idents, map).0,
                    post_pattern: normalize_types_in_pattern(
                        a.post_pattern,
                        resolved_idents,
                        map,
                    ),
                })
                .collect(),
        ),
    }
}
