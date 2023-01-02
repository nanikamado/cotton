mod type_check;
pub mod type_util;

pub use self::type_check::{
    simplify_subtype_rel, GlobalVariableType, LocalVariableType, ResolvedIdent,
    TypeVariableMap, VariableId, VariableRequirement,
};
use self::type_check::{type_check, TypeCheckResult};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step1::name_id::Name;
use crate::ast_step1::token_map::TokenMap;
use crate::ast_step2::types::{Type, TypeConstructor, TypeUnit, TypeVariable};
use crate::ast_step2::{self, Pattern, PatternUnit};
use crate::errors::CompileError;
use fxhash::FxHashMap;

/// Difference between `ast_step2::Ast` and `ast_step3::Ast`:
/// - The names of variables are resolved.
/// - Implicit parameters are converted to explicit parameters.
#[derive(Debug, PartialEq)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: DeclId,
    pub types_of_global_decls: FxHashMap<VariableId, GlobalVariableType>,
    pub types_of_local_decls: FxHashMap<VariableId, LocalVariableType>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl {
    pub name: Name,
    pub value: ExprWithType,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Copy)]
pub enum VariableKind {
    Local,
    Global,
    Constructor,
    Intrinsic,
    IntrinsicConstructor,
}

pub type ExprWithType = (Expr, Type);

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Lambda(Vec<FnArm>),
    Number(String),
    StrLiteral(String),
    Ident {
        name: String,
        variable_id: VariableId,
        variable_kind: VariableKind,
    },
    Call(Box<ExprWithType>, Box<ExprWithType>),
    DoBlock(Vec<ExprWithType>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm {
    pub pattern: Vec<Pattern<Type>>,
    pub expr: ExprWithType,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl {
    pub name: Name,
    pub field_len: usize,
    pub decl_id: DeclId,
}

impl Ast {
    pub fn from(
        mut ast: ast_step2::Ast,
        token_map: &mut TokenMap,
    ) -> Result<(Self, FxHashMap<IdentId, ResolvedIdent>), CompileError> {
        let TypeCheckResult {
            resolved_idents,
            global_variable_types,
            mut local_variable_types,
            type_variable_map: mut map,
        } = type_check(&mut ast, token_map)?;
        let (variable_decl, entry_point) = variable_decl(
            ast.variable_decl,
            ast.entry_point,
            &resolved_idents,
            &mut map,
            &mut local_variable_types,
        );
        for v in &variable_decl {
            log::debug!(
                "type_ {} : {}",
                v.name,
                global_variable_types[&VariableId::Decl(v.decl_id)].t
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
                entry_point,
                types_of_global_decls: global_variable_types,
                types_of_local_decls: local_variable_types,
            },
            resolved_idents,
        ))
    }
}

fn variable_decl(
    variable_decls: Vec<ast_step2::VariableDecl>,
    entry_point: DeclId,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
    types_of_decls: &mut FxHashMap<VariableId, LocalVariableType>,
) -> (Vec<VariableDecl>, DeclId) {
    let variable_decls = variable_decls
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
                    VariableId::Decl(decl_id),
                    LocalVariableType {
                        t: t.clone(),
                        toplevel: d.decl_id,
                    },
                );
                value = Expr::Lambda(vec![FnArm {
                    pattern: vec![vec![PatternUnit::Binder(
                        name,
                        decl_id,
                        t.clone(),
                    )]],
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
        .collect();
    (variable_decls, entry_point)
}

fn expr(
    (e, t, _): ast_step2::ExprWithTypeAndSpan<TypeVariable>,
    resolved_idents: &FxHashMap<IdentId, ResolvedIdent>,
    map: &mut TypeVariableMap,
) -> ExprWithType {
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
                                normalize_types_in_pattern(p, map)
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
                name.last().unwrap().0.clone(),
                &resolved_item,
                map.find(t),
                resolved_idents,
            )
        }
        ast_step2::Expr::ResolvedIdent { decl_id, .. } => Expr::Ident {
            name: "unique".to_string(),
            variable_id: VariableId::Decl(decl_id),
            variable_kind: VariableKind::Local,
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
) -> Expr {
    let mut value = Expr::Ident {
        name,
        variable_id: resolved_ident.variable_id,
        variable_kind: resolved_ident.variable_kind,
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

fn normalize_types_in_pattern(
    pattern: Pattern<TypeVariable>,
    map: &mut TypeVariableMap,
) -> Pattern<Type> {
    pattern
        .into_iter()
        .map(|p| normalize_types_in_pattern_unit(p, map))
        .collect()
}

fn normalize_types_in_pattern_unit(
    pattern: PatternUnit<TypeVariable>,
    map: &mut TypeVariableMap,
) -> PatternUnit<Type> {
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
                    .map(|p| normalize_types_in_pattern(p, map))
                    .collect(),
            }
        }
        PatternUnit::Underscore => PatternUnit::Underscore,
        PatternUnit::TypeRestriction(p, t) => {
            PatternUnit::TypeRestriction(normalize_types_in_pattern(p, map), t)
        }
    }
}
