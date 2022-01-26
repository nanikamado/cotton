pub(crate) mod intrinsics;
mod simplify;
mod type_util;

use self::type_util::construct_type;
use crate::ast1::{
    decl_id::DeclId, ident_id::IdentId, types, types::TypeUnit, Ast,
    DataDeclaration, Expr, FnArm, IncompleteType, Pattern,
    Requirements,
};
use fxhash::FxHashMap;
use intrinsics::INTRINSIC_VARIABLES;
use itertools::multiunzip;
use std::collections::BTreeSet;
use std::vec;

type Resolved = Vec<(IdentId, DeclId)>;

pub fn type_check(ast: &Ast) -> FxHashMap<IdentId, DeclId> {
    let mut toplevels: FxHashMap<String, Vec<Toplevel>> =
        FxHashMap::default();
    for (name, ts) in &*INTRINSIC_VARIABLES {
        *toplevels.entry(name.clone()).or_default() = ts
            .iter()
            .map(|(t, decl_id)| Toplevel {
                incomplete: t.clone().into(),
                face: None,
                resolved_idents: Default::default(),
                decl_id: *decl_id,
            })
            .collect();
    }
    for d in &ast.data_declarations {
        let d_type: types::Type = constructor_type(d.clone()).into();
        toplevels.entry(d.name.clone()).or_default().push(Toplevel {
            incomplete: d_type.into(),
            face: None,
            resolved_idents: Default::default(),
            decl_id: d.decl_id,
        });
    }
    let mut resolved_idents = FxHashMap::default();
    for d in &ast.declarations {
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
        toplevels.entry(d.identifier.clone()).or_default().push(
            Toplevel {
                incomplete: simplify::simplify_type(t.clone())
                    .unwrap(),
                face,
                resolved_idents: Default::default(),
                decl_id: d.decl_id,
            },
        );
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

struct Toplevel {
    incomplete: IncompleteType,
    face: Option<IncompleteType>,
    resolved_idents: FxHashMap<IdentId, DeclId>,
    decl_id: DeclId,
}

fn resolve_names(
    mut toplevels: FxHashMap<String, Vec<Toplevel>>,
) -> FxHashMap<String, Vec<Toplevel>> {
    loop {
        // (name, num, variable req num, type)
        let mut resolved: Option<(
            &String,
            usize,
            IncompleteType,
            IdentId,
            DeclId,
        )> = None;
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
                                // if is_recursive {
                                //     incomplete
                                //         .requirements
                                //         .subtype_relation
                                //         .insert((
                                //             req_t.clone(),
                                //             cand_t.constructor,
                                //         ));
                                // }
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
                            resolved = Some((
                                name,
                                t_index,
                                successes[0].0.clone(),
                                successes[0].2,
                                successes[0].3,
                            ));
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
        if let Some((name, v_index, r, ident_id, decl_id)) = resolved
        {
            let name = name.clone();
            let topl =
                &mut toplevels.get_mut(&name).unwrap()[v_index];
            debug_assert_eq!(
                simplify::simplify_type(r.clone()).unwrap(),
                r.clone()
            );
            topl.incomplete = r;
            topl.resolved_idents.insert(ident_id, decl_id);
        } else {
            break;
        }
    }
    toplevels
}

fn constructor_type(d: DataDeclaration) -> TypeUnit {
    let field_types: Vec<_> =
        (0..d.field_len).map(|_| TypeUnit::new_variable()).collect();
    let mut t = TypeUnit::Normal(
        d.name,
        field_types.iter().map(|t| t.clone().into()).collect(),
    );
    for field in field_types.into_iter().rev() {
        t = TypeUnit::Fn(field.into(), t.into())
    }
    t
}

fn min_type(
    expr: &Expr,
) -> Result<(IncompleteType, Resolved), &'static str> {
    Ok(min_type_incomplite(expr))
}

fn min_type_incomplite(expr: &Expr) -> (IncompleteType, Resolved) {
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
        Expr::Identifier { info, ident_id, .. } => {
            let t: types::Type = TypeUnit::new_variable().into();
            (
                IncompleteType {
                    constructor: t.clone(),
                    requirements: Requirements {
                        variable_requirements: vec![(
                            info.to_string(),
                            t,
                            *ident_id,
                        )],
                        subtype_relation: BTreeSet::new(),
                    },
                },
                Default::default(),
            )
        }
        Expr::Declaration(_) => {
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

fn multi_expr_min_type(exprs: &[Expr]) -> (IncompleteType, Resolved) {
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

fn arm_min_type(
    arm: &FnArm,
) -> ((types::Type, types::Type), Requirements, Resolved) {
    let (body_type, mut resolved_idents) =
        multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(pattern_to_type).unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type = TypeUnit::Fn(pattern_type.clone(), arm_type).into()
    }
    let bindings: FxHashMap<String, (DeclId, types::Type)> = bindings
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
            resolved_idents.push((p.2, a.0));
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

fn pattern_to_type(
    p: &Pattern,
) -> (types::Type, Vec<(String, DeclId, types::Type)>) {
    match p {
        Pattern::Number(_) => (construct_type("Num"), Vec::new()),
        Pattern::StrLiteral(_) => {
            (construct_type("String"), Vec::new())
        }
        Pattern::Constructor(name, cs) => {
            let (types, bindings): (Vec<_>, Vec<_>) =
                cs.iter().map(pattern_to_type).unzip();
            (
                TypeUnit::Normal(name.clone(), types).into(),
                bindings.concat(),
            )
        }
        Pattern::Binder(name, decl_id) => {
            let t: types::Type = TypeUnit::new_variable().into();
            (t.clone(), vec![(name.to_string(), *decl_id, t)])
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
        ast1::{
            decl_id::new_decl_id,
            ident_id::new_ident_id,
            types::{Type, TypeUnit},
            IncompleteType, Requirements,
        },
        parse::infix_type_sequence,
        type_check::resolve_names,
    };
    use fxhash::FxHashMap;
    use std::collections::BTreeSet;
    use stripmargin::StripMargin;

    #[test]
    fn resolve_1() {
        // FxHashMap<String, Vec<Toplevel>>,
        let top_levels: FxHashMap<String, Vec<Toplevel>> = vec![
            (
                ("main".to_string()),
                vec![Toplevel {
                    incomplete: IncompleteType {
                        constructor: construct_type("()"),
                        requirements: Requirements {
                            variable_requirements: vec![
                                (
                                    "default".to_string(),
                                    construct_type("Hoge"),
                                    new_ident_id(),
                                ),
                                (
                                    "default".to_string(),
                                    construct_type("Fuga"),
                                    new_ident_id(),
                                ),
                            ],
                            subtype_relation: BTreeSet::new(),
                        },
                    },
                    face: None,
                    resolved_idents: Default::default(),
                    decl_id: new_decl_id(),
                }],
            ),
            (
                ("default".to_string()),
                vec![
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor: construct_type("Hoge"),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: new_decl_id(),
                    }),
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor: construct_type("Fuga"),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: new_decl_id(),
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
            |resolved: {IdentId(0): DeclId(1), IdentId(1): DeclId(2)}
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
        // FxHashMap<String, Vec<Toplevel>>,
        let top_levels: FxHashMap<String, Vec<Toplevel>> = vec![
            (
                ("main".to_string()),
                vec![Toplevel {
                    incomplete: IncompleteType {
                        constructor: construct_type("()"),
                        requirements: Requirements {
                            variable_requirements: vec![
                                (
                                    "greet".to_string(),
                                    construct_type("Hoge -> String"),
                                    new_ident_id(),
                                ),
                                (
                                    "greet".to_string(),
                                    construct_type("Fuga -> String"),
                                    new_ident_id(),
                                ),
                            ],
                            subtype_relation: BTreeSet::new(),
                        },
                    },
                    face: None,
                    resolved_idents: Default::default(),
                    decl_id: new_decl_id(),
                }],
            ),
            (
                ("greet".to_string()),
                vec![
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor: construct_type(
                                "Hoge -> String",
                            ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: new_decl_id(),
                    }),
                    (Toplevel {
                        incomplete: IncompleteType {
                            constructor: construct_type(
                                "Fuga -> String",
                            ),
                            requirements: Default::default(),
                        },
                        face: None,
                        resolved_idents: Default::default(),
                        decl_id: new_decl_id(),
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
            |resolved: {IdentId(0): DeclId(1), IdentId(1): DeclId(2)}
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
        toplevels: FxHashMap<String, Vec<Toplevel>>,
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

    fn construct_type(s: &str) -> Type {
        let (_, type_seq) = infix_type_sequence(s).unwrap();
        let inc_t: IncompleteType =
            (type_seq, Default::default()).into();
        inc_t.constructor
    }

    #[test]
    fn construct_type_test_1() {
        assert_eq!(
            construct_type("Foge"),
            TypeUnit::Normal("Foge".to_string(), Vec::new()).into()
        )
    }

    #[test]
    fn construct_type_test_2() {
        assert_eq!(
            construct_type("Foge -> String"),
            TypeUnit::Fn(
                construct_type("Foge").into(),
                construct_type("String").into()
            )
            .into()
        )
    }
}
