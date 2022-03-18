pub(crate) mod intrinsics;
mod simplify;
mod type_util;

use self::type_util::construct_type;
use crate::ast2::{
    decl_id::DeclId, ident_id::IdentId, types, types::TypeUnit,
};
use crate::ast2::{Ast, DataDecl, Expr, FnArm, Pattern, TypeIdent};
use crate::ast2::{IncompleteType, Requirements};
use crate::type_check::intrinsics::IntrinsicVariable;
use fxhash::FxHashMap;
use itertools::multiunzip;
use std::collections::BTreeSet;
use std::fmt::Display;
use std::vec;
use strum::IntoEnumIterator;

type Resolved = Vec<(IdentId, VariableId)>;

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum VariableId {
    Decl(DeclId),
    Intrinsic(IntrinsicVariable),
}

impl Display for VariableId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => a.fmt(f),
            VariableId::Intrinsic(a) => a.fmt(f),
        }
    }
}

impl std::fmt::Debug for VariableId {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            VariableId::Decl(a) => write!(f, "VariableId({})", a),
            VariableId::Intrinsic(a) => {
                write!(f, "VariableId({})", a)
            }
        }
    }
}

pub fn type_check(ast: &Ast) -> FxHashMap<IdentId, VariableId> {
    let mut toplevels: FxHashMap<&str, Vec<Toplevel>> =
        FxHashMap::default();
    for v in IntrinsicVariable::iter() {
        toplevels.entry(v.to_str()).or_default().push(Toplevel {
            incomplete: v.to_type().clone().into(),
            face: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Intrinsic(v),
        });
    }
    for d in &ast.data_decl {
        let d_type: types::Type = constructor_type(*d).into();
        toplevels.entry(d.name).or_default().push(Toplevel {
            incomplete: d_type.into(),
            face: None,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
        });
    }
    let mut resolved_idents = FxHashMap::default();
    for d in &ast.variable_decl {
        let (mut t, resolved) = min_type(&d.value).unwrap();
        resolved_idents.extend(resolved);
        let face = if let Some(annotation) = &d.type_annotation {
            let annotation = annotation.clone().change_variable_num();
            t.requirements.subtype_relation.insert((
                t.constructor.clone(),
                annotation.constructor.clone(),
            ));
            t.requirements.subtype_relation.insert((
                annotation.constructor.clone(),
                t.constructor.clone(),
            ));
            t.requirements =
                t.requirements.merge(annotation.requirements.clone());
            Some(annotation)
        } else {
            None
        };
        toplevels.entry(d.ident).or_default().push(Toplevel {
            incomplete: simplify::simplify_type(t.clone()).unwrap(),
            face,
            resolved_idents: Default::default(),
            decl_id: VariableId::Decl(d.decl_id),
        });
    }
    for (name, top) in &toplevels {
        log::debug!("{} : ", name);
        for t in top {
            log::debug!("resolved: {:?}", t.resolved_idents);
            if let Some(f) = &t.face {
                log::debug!("face: {}", f);
                log::debug!("incomplete: {}", t.incomplete);
            } else {
                log::debug!("not face: {}", t.incomplete);
            }
        }
    }
    let toplevels = resolve_names(toplevels);
    log::debug!("------------------------------");
    for (name, top) in toplevels {
        log::debug!("{} : ", name);
        for t in top {
            log::debug!("{}", t.incomplete);
            log::debug!("resolved: {:?}\n", t.resolved_idents);
            resolved_idents.extend(t.resolved_idents)
        }
    }
    resolved_idents
}

struct Toplevel<'a> {
    incomplete: IncompleteType<'a>,
    face: Option<IncompleteType<'a>>,
    resolved_idents: FxHashMap<IdentId, VariableId>,
    decl_id: VariableId,
}

fn resolve_names<'a>(
    mut toplevels: FxHashMap<&'a str, Vec<Toplevel<'a>>>,
) -> FxHashMap<&'a str, Vec<Toplevel<'a>>> {
    struct ResolvedType<'a> {
        name: &'a str,
        index: usize,
        incomplete_type: IncompleteType<'a>,
        ident: IdentId,
        decl: VariableId,
    }
    loop {
        let mut resolved: Option<ResolvedType> = None;
        'outer: for (name, types) in &toplevels {
            for (t_index, t) in types.iter().enumerate() {
                if !t.incomplete.resolved() {
                    for (req_i, (req_name, req_t, _)) in t
                        .incomplete
                        .requirements
                        .variable_requirements
                        .iter()
                        .enumerate()
                    {
                        let candidates = &toplevels[&req_name[..]];
                        if candidates.iter().all(|c| {
                            c.face.is_none()
                                && !c.incomplete.resolved()
                                && t.decl_id != c.decl_id
                        }) {
                            continue;
                        }
                        let successes: Vec<_> = candidates
                            .iter()
                            .filter_map(|cand| {
                                let mut cand_t =
                                    if let Some(face) = &cand.face {
                                        face.clone()
                                    } else {
                                        cand.incomplete.clone()
                                    };
                                let is_recursive =
                                    t.decl_id == cand.decl_id;
                                if !is_recursive {
                                    cand_t =
                                        cand_t.change_variable_num();
                                }
                                let cand_resolved = cand_t.resolved();
                                let mut incomplete =
                                    t.incomplete.clone();
                                let removed_req = incomplete
                                    .requirements
                                    .variable_requirements
                                    .remove(req_i);
                                incomplete
                                    .requirements
                                    .subtype_relation
                                    .insert((
                                        cand_t.constructor.clone(),
                                        req_t.clone(),
                                    ));
                                incomplete
                                    .requirements
                                    .subtype_relation
                                    .extend(
                                        cand_t
                                            .requirements
                                            .subtype_relation,
                                    );
                                simplify::simplify_type(incomplete)
                                    .map(|t| {
                                        (
                                            t,
                                            cand_resolved
                                                || is_recursive,
                                            removed_req.2,
                                            cand.decl_id,
                                        )
                                    })
                            })
                            .collect();
                        if successes.len() == 1 && successes[0].1 {
                            resolved = Some(ResolvedType {
                                name,
                                index: t_index,
                                incomplete_type: successes[0]
                                    .0
                                    .clone(),
                                ident: successes[0].2,
                                decl: successes[0].3,
                            });
                            break 'outer;
                        } else if successes.is_empty() {
                            log::debug!(
                                "all of {} has failed in {}[{}]",
                                req_name,
                                name,
                                t_index
                            );
                            log::debug!("req_t: {}", req_t);
                            log::debug!("t -> {}", t.incomplete);
                        }
                    }
                }
            }
        }
        if let Some(r) = resolved {
            let topl =
                &mut toplevels.get_mut(&r.name).unwrap()[r.index];
            debug_assert_eq!(
                simplify::simplify_type(r.incomplete_type.clone())
                    .unwrap(),
                r.incomplete_type
            );
            topl.incomplete = r.incomplete_type;
            topl.resolved_idents.insert(r.ident, r.decl);
        } else {
            break;
        }
    }
    toplevels
}

fn constructor_type<'a>(d: DataDecl<'a>) -> TypeUnit<'a> {
    let field_types: Vec<_> =
        (0..d.field_len).map(|_| TypeUnit::new_variable()).collect();
    let mut t = TypeUnit::Normal {
        name: d.name,
        args: field_types.iter().map(|t| t.clone().into()).collect(),
        id: TypeIdent::DeclId(d.decl_id, &d.name),
    };
    for field in field_types.into_iter().rev() {
        t = TypeUnit::Fn(field.into(), t.into())
    }
    t
}

fn min_type<'a>(
    expr: &'a Expr,
) -> Result<(IncompleteType<'a>, Resolved), &'a str> {
    Ok(min_type_incomplite(expr))
}

fn min_type_incomplite<'a>(
    expr: &'a Expr,
) -> (IncompleteType<'a>, Resolved) {
    match expr {
        Expr::Lambda(arms) => {
            let (arm_types, requirements, resolved_idents): (
                Vec<_>,
                Vec<_>,
                Vec<_>,
            ) = multiunzip(arms.iter().map(arm_min_type));
            let resolved_idents =
                resolved_idents.into_iter().flatten().collect();
            let (args, rtns): (Vec<types::Type>, Vec<types::Type>) =
                arm_types.into_iter().unzip();
            let constructor = if args.len() == 1 {
                TypeUnit::Fn(
                    args.into_iter().next().unwrap(),
                    rtns.into_iter().next().unwrap(),
                )
            } else {
                TypeUnit::Fn(
                    args.into_iter().flatten().collect(),
                    rtns.into_iter().flatten().collect(),
                )
            };
            (
                IncompleteType {
                    constructor: constructor.into(),
                    requirements: marge_requirements(requirements),
                },
                resolved_idents,
            )
        }
        Expr::Number(_) => {
            (construct_type("Num").into(), Default::default())
        }
        Expr::StrLiteral(_) => {
            (construct_type("String").into(), Default::default())
        }
        Expr::Ident {
            name: info,
            ident_id,
            ..
        } => {
            let t: types::Type = TypeUnit::new_variable().into();
            (
                IncompleteType {
                    constructor: t.clone(),
                    requirements: Requirements {
                        variable_requirements: vec![(
                            info, t, *ident_id,
                        )],
                        subtype_relation: BTreeSet::new(),
                    },
                },
                Default::default(),
            )
        }
        Expr::Decl(_) => {
            (construct_type("()").into(), Default::default())
        }
        Expr::Call(f, a) => {
            let (f_t, resolved1) = min_type_incomplite(f);
            let (a_t, resolved2) = min_type_incomplite(a);
            let b: types::Type = TypeUnit::new_variable().into();
            let c: types::Type = TypeUnit::new_variable().into();
            // c -> b
            let cb_fn = TypeUnit::Fn(c.clone(), b.clone());
            // f < c -> b
            let f_sub_cb = Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: {
                    [(f_t.constructor, cb_fn.into())]
                        .iter()
                        .cloned()
                        .collect()
                },
            };
            // a < c
            let a_sub_c = Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: [(a_t.constructor, c)]
                    .iter()
                    .cloned()
                    .collect(),
            };
            (
                IncompleteType {
                    constructor: b,
                    requirements: marge_requirements(vec![
                        f_sub_cb,
                        a_sub_c,
                        f_t.requirements,
                        a_t.requirements,
                    ]),
                },
                [resolved1, resolved2].concat(),
            )
        }
        Expr::Unit => {
            (construct_type("()").into(), Default::default())
        }
    }
}

fn multi_expr_min_type<'a>(
    exprs: &'a [Expr],
) -> (IncompleteType<'a>, Resolved) {
    let mut req = Requirements::default();
    let mut resolved_idents = Vec::default();
    let t = exprs
        .iter()
        .map(|e| {
            let (t, resolved) = min_type_incomplite(e);
            resolved_idents.extend(resolved);
            req = marge_requirements(vec![
                req.clone(),
                t.clone().requirements,
            ]);
            t
        })
        .collect::<Vec<_>>();
    let t = t.last().unwrap().clone();
    (
        IncompleteType {
            constructor: t.constructor,
            requirements: req,
        },
        resolved_idents,
    )
}

fn marge_requirements(
    requirements: Vec<Requirements>,
) -> Requirements {
    let mut rst = Requirements::default();
    for mut r in requirements {
        rst.variable_requirements
            .append(&mut r.variable_requirements);
        rst.subtype_relation.append(&mut r.subtype_relation);
    }
    rst
}

fn arm_min_type<'a>(
    arm: &'a FnArm,
) -> (
    (types::Type<'a>, types::Type<'a>),
    Requirements<'a>,
    Resolved,
) {
    let (body_type, mut resolved_idents) =
        multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type = TypeUnit::Fn(pattern_type.clone(), arm_type).into()
    }
    let bindings: FxHashMap<&str, (DeclId, types::Type)> = bindings
        .into_iter()
        .flatten()
        .map(|(n, i, t)| (n, (i, t)))
        .collect();
    let mut variable_requirements = Vec::new();
    let mut subtype_requirement = Vec::new();
    for p in body_type.requirements.variable_requirements.into_iter()
    {
        if let Some(a) = bindings.get(&p.0) {
            subtype_requirement.push((a.1.clone(), p.1.clone()));
            subtype_requirement.push((p.1, a.1.clone()));
            resolved_idents.push((p.2, VariableId::Decl(a.0)));
        } else {
            variable_requirements.push(p);
        }
    }
    (
        (types[0].clone(), arm_type),
        Requirements {
            variable_requirements,
            subtype_relation: {
                let mut tmp = body_type.requirements.subtype_relation;
                tmp.append(
                    &mut subtype_requirement.into_iter().collect(),
                );
                tmp
            },
        },
        resolved_idents,
    )
}

fn pattern_to_type<'a>(
    p: &'a Pattern,
) -> (types::Type<'a>, Vec<(&'a str, DeclId, types::Type<'a>)>) {
    match p {
        Pattern::Number(_) => (construct_type("Num"), Vec::new()),
        Pattern::StrLiteral(_) => {
            (construct_type("String"), Vec::new())
        }
        Pattern::Constructor { id, args } => {
            let (types, bindings): (Vec<_>, Vec<_>) =
                args.iter().map(pattern_to_type).unzip();
            (
                TypeUnit::Normal {
                    name: id.name(),
                    args: types,
                    id: (*id).into(),
                }
                .into(),
                bindings.concat(),
            )
        }
        Pattern::Binder(name, decl_id) => {
            let t: types::Type = TypeUnit::new_variable().into();
            (t.clone(), vec![(name, *decl_id, t)])
        }
        Pattern::Underscore => {
            (TypeUnit::new_variable().into(), Vec::new())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Toplevel;
    use crate::{
        ast1, ast2,
        ast2::{
            decl_id::{self, new_decl_id},
            ident_id::new_ident_id,
            IncompleteType, Requirements,
        },
        parse,
        type_check::{
            resolve_names, type_util::construct_type_with_variables,
            VariableId,
        },
    };
    use fxhash::FxHashMap;
    use std::collections::BTreeSet;
    use stripmargin::StripMargin;

    #[test]
    fn resolve_1() {
        let ast: ast1::Ast =
            parse::parse("data Hoge\ndata Fuga\nmain = ()")
                .unwrap()
                .1
                .into();
        let ast: ast2::Ast = ast.into();
        let data_decl_map: FxHashMap<&str, decl_id::DeclId> = ast
            .data_decl
            .iter()
            .map(|d| (&d.name[..], d.decl_id))
            .collect();
        let top_levels: FxHashMap<&str, Vec<Toplevel>> = vec![
            (
                ("main"),
                vec![Toplevel {
                    incomplete: IncompleteType {
                        constructor: construct_type_with_variables(
                            "()",
                            &[],
                            &data_decl_map,
                        ),
                        requirements: Requirements {
                            variable_requirements: vec![
                                (
                                    "default",
                                    construct_type_with_variables(
                                        "Hoge",
                                        &[],
                                        &data_decl_map,
                                    ),
                                    new_ident_id(),
                                ),
                                (
                                    "default",
                                    construct_type_with_variables(
                                        "Fuga",
                                        &[],
                                        &data_decl_map,
                                    ),
                                    new_ident_id(),
                                ),
                            ],
                            subtype_relation: BTreeSet::new(),
                        },
                    },
                    face: None,
                    resolved_idents: Default::default(),
                    decl_id: VariableId::Decl(new_decl_id()),
                }],
            ),
            (
                ("default"),
                vec![
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor:
                                construct_type_with_variables(
                                    "Hoge",
                                    &[],
                                    &data_decl_map,
                                ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: VariableId::Decl(new_decl_id()),
                    }),
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor:
                                construct_type_with_variables(
                                    "Fuga",
                                    &[],
                                    &data_decl_map,
                                ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: VariableId::Decl(new_decl_id()),
                    }),
                ],
            ),
        ]
        .into_iter()
        .collect();
        let s = debug_toplevels(resolve_names(top_levels));
        assert_eq!(
            s,
            "main : 
            |resolved: {IdentId(0): VariableId(4), IdentId(1): VariableId(5)}
            |not face: () forall
            |--
            |default : 
            |resolved: {}
            |not face: Hoge forall
            |--
            |resolved: {}
            |not face: Fuga forall
            |--
            |"
            .strip_margin()
        );
    }

    #[test]
    fn resolve_2() {
        let ast: ast1::Ast =
            parse::parse("data Hoge\ndata Fuga\nmain = ()")
                .unwrap()
                .1
                .into();
        let ast: ast2::Ast = ast.into();
        let data_decl_map: FxHashMap<&str, decl_id::DeclId> = ast
            .data_decl
            .iter()
            .map(|d| (&d.name[..], d.decl_id))
            .collect();
        let top_levels: FxHashMap<&str, Vec<Toplevel>> = vec![
            (
                ("main"),
                vec![Toplevel {
                    incomplete: IncompleteType {
                        constructor: construct_type_with_variables(
                            "()",
                            &[],
                            &data_decl_map,
                        ),
                        requirements: Requirements {
                            variable_requirements: vec![
                                (
                                    "greet",
                                    construct_type_with_variables(
                                        "Hoge -> String",
                                        &[],
                                        &data_decl_map,
                                    ),
                                    new_ident_id(),
                                ),
                                (
                                    "greet",
                                    construct_type_with_variables(
                                        "Fuga -> String",
                                        &[],
                                        &data_decl_map,
                                    ),
                                    new_ident_id(),
                                ),
                            ],
                            subtype_relation: BTreeSet::new(),
                        },
                    },
                    face: None,
                    resolved_idents: Default::default(),
                    decl_id: VariableId::Decl(new_decl_id()),
                }],
            ),
            (
                ("greet"),
                vec![
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor:
                                construct_type_with_variables(
                                    "Hoge -> String",
                                    &[],
                                    &data_decl_map,
                                ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: VariableId::Decl(new_decl_id()),
                    }),
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor:
                                construct_type_with_variables(
                                    "Fuga -> String",
                                    &[],
                                    &data_decl_map,
                                ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: VariableId::Decl(new_decl_id()),
                    }),
                ],
            ),
        ]
        .into_iter()
        .collect();
        let s = debug_toplevels(resolve_names(top_levels));
        assert_eq!(
            s,
            r#"main : 
            |resolved: {IdentId(0): VariableId(4), IdentId(1): VariableId(5)}
            |not face: () forall
            |--
            |greet : 
            |resolved: {}
            |not face: Hoge -> String forall
            |--
            |resolved: {}
            |not face: Fuga -> String forall
            |--
            |"#
            .strip_margin()
        );
    }

    fn debug_toplevels(
        toplevels: FxHashMap<&str, Vec<Toplevel>>,
    ) -> String {
        let mut ret = String::new();
        for (name, top) in &toplevels {
            ret += &format!("{} : \n", name);
            for t in top {
                ret +=
                    &format!("resolved: {:?}\n", t.resolved_idents);
                if let Some(f) = &t.face {
                    ret += &format!("face: {}\n", f);
                    ret += &format!("incomplete: {}\n", t.incomplete);
                } else {
                    ret += &format!("not face: {}\n", t.incomplete);
                }
            }
        }
        ret
    }
}
