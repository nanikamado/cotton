mod type_check;
pub mod type_util;

pub use self::type_check::{
    simplify_subtype_rel, type_check, ResolvedIdents, TypeVariableMap,
    VariableId, VariableRequirement,
};
use crate::{
    ast_step2::{
        self,
        decl_id::DeclId,
        types::{Type, TypeUnit, TypeVariable},
        Pattern, PatternUnit, TypeConstructor,
    },
    ast_step5::VariableKind,
};
use fxhash::FxHashMap;

/// # Difference between `ast_step2::Ast` and `ast_step3::Ast`
/// - The names of variables are resolved.
/// - Implicit parameters are converted to explicit parameters.
#[derive(Debug, PartialEq)]
pub struct Ast<'a> {
    pub variable_decl: Vec<VariableDecl<'a>>,
    pub data_decl: Vec<DataDecl<'a>>,
    pub entry_point: DeclId,
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
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
        variable_kind: VariableKind,
    },
    Call(Box<ExprWithType<'a>>, Box<ExprWithType<'a>>),
    DoBlock(Vec<ExprWithType<'a>>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct FnArm<'a> {
    pub pattern: Vec<Pattern<'a, Type<'a>>>,
    pub expr: ExprWithType<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
    pub decl_id: DeclId,
}

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step2::Ast<'a>) -> Self {
        let (resolved_idents, types_of_decls, _subtype_relations, mut map) =
            type_check(&ast);
        let (variable_decl, entry_point) = variable_decl(
            ast.variable_decl,
            &ast.data_decl,
            ast.entry_point,
            &resolved_idents,
            &mut map,
        );
        for v in &variable_decl {
            log::debug!("type_ {} : {}", v.name, types_of_decls[&v.decl_id]);
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
        Self {
            variable_decl,
            data_decl,
            entry_point,
        }
    }
}

fn variable_decl<'a>(
    variable_decls: Vec<ast_step2::VariableDecl<'a>>,
    data_decls: &[ast_step2::DataDecl<'a>],
    entry_point: DeclId,
    resolved_idents: &ResolvedIdents<'a>,
    map: &mut TypeVariableMap<'a>,
) -> (Vec<VariableDecl<'a>>, DeclId) {
    let data_decls: FxHashMap<DeclId, &ast_step2::DataDecl<'a>> = data_decls
        .iter()
        .map(|d| {
            let did = d.decl_id;
            (did, d)
        })
        .collect();
    let variable_decls = variable_decls
        .into_iter()
        .map(|d| {
            let (mut value, mut value_t) =
                expr(d.value, &data_decls, resolved_idents, map);
            for (name, t, decl_id) in d.implicit_parameters.into_iter().rev() {
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

fn expr<'a, 'b>(
    (e, t): ast_step2::ExprWithType<'a, TypeVariable>,
    data_decls: &FxHashMap<DeclId, &'b ast_step2::DataDecl<'a>>,
    resolved_idents: &ResolvedIdents<'a>,
    map: &mut TypeVariableMap<'a>,
) -> ExprWithType<'a> {
    let e = match e {
        ast_step2::Expr::Lambda(arms) => Expr::Lambda(
            arms.into_iter()
                .map(|a| {
                    let e = expr(a.expr, data_decls, resolved_idents, map);
                    FnArm {
                        pattern: a
                            .pattern
                            .into_iter()
                            .map(|p| normalize_types_in_pattern(p, map))
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
            let mut value = Expr::Ident {
                name,
                variable_id: resolved_item.variable_id,
                variable_kind: resolved_item.variable_kind,
            };
            let mut ts = Vec::new();
            let mut fn_t = map.find(t);
            for (_, _, implicit_arg_t, _) in
                resolved_item.implicit_args.iter().rev()
            {
                fn_t = TypeUnit::Fn(implicit_arg_t.clone(), fn_t).into();
                ts.push(fn_t.clone());
            }
            for ((_, name, implicit_arg_t, resolved_item), fn_t) in
                resolved_item.implicit_args.iter().zip(ts.into_iter().rev())
            {
                let variable_id = resolved_item.variable_id;
                value = Expr::Call(
                    Box::new((value, fn_t)),
                    Box::new((
                        Expr::Ident {
                            name,
                            variable_id,
                            variable_kind: resolved_item.variable_kind,
                        },
                        implicit_arg_t.clone(),
                    )),
                );
            }
            value
        }
        ast_step2::Expr::Call(f, a) => Expr::Call(
            expr(*f, data_decls, resolved_idents, map).into(),
            expr(*a, data_decls, resolved_idents, map).into(),
        ),
        ast_step2::Expr::Do(es) => Expr::DoBlock(
            es.into_iter()
                .map(|e| expr(e, data_decls, resolved_idents, map))
                .collect(),
        ),
    };
    (e, lift_recursive_alias(map.find(t)))
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
    pattern: Pattern<'a, TypeVariable>,
    map: &mut TypeVariableMap<'a>,
) -> Pattern<'a, Type<'a>> {
    pattern
        .into_iter()
        .map(|p| normalize_types_in_pattern_unit(p, map))
        .collect()
}

fn normalize_types_in_pattern_unit<'a>(
    pattern: PatternUnit<'a, TypeVariable>,
    map: &mut TypeVariableMap<'a>,
) -> PatternUnit<'a, Type<'a>> {
    match pattern {
        PatternUnit::Binder(name, ident_id, t) => {
            PatternUnit::Binder(name, ident_id, map.find(t))
        }
        PatternUnit::I64(a) => PatternUnit::I64(a),
        PatternUnit::Str(a) => PatternUnit::Str(a),
        PatternUnit::Constructor { id, args } => PatternUnit::Constructor {
            id,
            args: args
                .into_iter()
                .map(|p| normalize_types_in_pattern(p, map))
                .collect(),
        },
        PatternUnit::Underscore => PatternUnit::Underscore,
        PatternUnit::TypeRestriction(p, t) => {
            PatternUnit::TypeRestriction(normalize_types_in_pattern(p, map), t)
        }
    }
}
