mod intrinsics;
mod simplify;
mod type_util;

use self::type_util::construct_type;
use crate::ast0::{DataDeclaration, Pattern};
use crate::ast1;
use crate::ast1::{
    ident_id::IdentId, Ast, Expr, FnArm, IncompleteType,
    Requirements, TypeUnit,
};
use fxhash::FxHashMap;
use intrinsics::INTRINSIC_VARIABLES;
use itertools::Itertools;
use std::collections::{BTreeSet, HashMap};
use std::vec;

pub fn type_check(ast: &Ast) -> FxHashMap<IdentId, usize> {
    let mut toplevels: FxHashMap<String, Vec<Toplevel>> =
        FxHashMap::default();
    for (name, ts) in &*INTRINSIC_VARIABLES {
        *toplevels.entry(name.clone()).or_default() = ts
            .iter()
            .map(|t| Toplevel {
                incomplete: t.clone().into(),
                face: None,
                resolved_idents: Default::default(),
            })
            .collect();
    }
    for d in &ast.data_declarations {
        let d_type: ast1::Type = constructor_type(d.clone()).into();
        toplevels.entry(d.name.clone()).or_default().push(Toplevel {
            incomplete: d_type.into(),
            face: None,
            resolved_idents: Default::default(),
        });
    }
    for d in &ast.declarations {
        let mut t = min_type(&d.value).unwrap();
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
            },
        );
    }
    for (name, top) in &toplevels {
        eprintln!("{} : ", name);
        for t in top {
            eprintln!("resolved: {:?}", t.resolved_idents);
            if let Some(f) = &t.face {
                eprintln!("face: {}", f);
                eprintln!("incomplete: {}", t.incomplete);
            } else {
                eprintln!("not face: {}", t.incomplete);
            }
        }
    }
    let toplevels = resolve_names(toplevels);
    eprintln!("------------------------------");
    let mut resolved_idents = FxHashMap::default();
    for (name, top) in toplevels {
        eprintln!("{} : ", name);
        for t in top {
            eprintln!("{}", t.incomplete);
            eprintln!("resolved: {:?}", t.resolved_idents);
            resolved_idents.extend(t.resolved_idents)
        }
    }
    resolved_idents
}

struct Toplevel {
    incomplete: IncompleteType,
    face: Option<IncompleteType>,
    resolved_idents: HashMap<IdentId, usize>,
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
            usize,
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
                        if candidates.iter().enumerate().all(
                            |(i, c)| {
                                c.face.is_none()
                                    && !c.incomplete.resolved()
                                    && !(name == req_name
                                        && t_index == i)
                            },
                        ) {
                            continue;
                        }
                        let successes: Vec<_> = candidates
                            .iter()
                            .enumerate()
                            .filter_map(|(i, cand)| {
                                let mut cand_t =
                                    if let Some(face) = &cand.face {
                                        face.clone()
                                    } else {
                                        cand.incomplete.clone()
                                    };
                                let is_recursive =
                                    name == req_name && t_index == i;
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
                                            i,
                                        )
                                    })
                            })
                            .collect();
                        if successes.len() == 1 && successes[0].1 {
                            resolved = Some((
                                name,
                                t_index,
                                successes[0].0.clone(),
                                successes[0].2.clone(),
                                successes[0].3.clone(),
                            ));
                            break 'outer;
                        } else if successes.is_empty() {
                            eprintln!(
                                "all of {} has failed in {}[{}]",
                                req_name, name, t_index
                            );
                            eprintln!("req_t: {}", req_t);
                            eprintln!("req_i: {}", req_i);
                            eprintln!("t -> {}", t.incomplete);
                        }
                    }
                }
            }
        }
        if let Some((name, v_index, r, ident_id, n)) = resolved {
            let name = name.clone();
            let topl =
                &mut toplevels.get_mut(&name).unwrap()[v_index];
            topl.incomplete = r;
            topl.resolved_idents.insert(ident_id, n);
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

fn min_type(expr: &Expr) -> Result<IncompleteType, &'static str> {
    Ok(min_type_incomplite(expr))
}

fn min_type_incomplite(expr: &Expr) -> IncompleteType {
    match expr {
        Expr::Lambda(arms) => {
            let (arm_types, requirements): (Vec<_>, Vec<_>) =
                arms.iter().map(|a| arm_min_type(a)).unzip();
            let (args, rtns): (Vec<ast1::Type>, Vec<ast1::Type>) =
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
            IncompleteType {
                constructor: constructor.into(),
                requirements: marge_requirements(requirements),
            }
        }
        Expr::Number(_) => construct_type("Num").into(),
        Expr::StrLiteral(_) => construct_type("String").into(),
        Expr::Identifier(n, id) => {
            let t: ast1::Type = TypeUnit::new_variable().into();
            IncompleteType {
                constructor: t.clone(),
                requirements: Requirements {
                    variable_requirements: vec![(
                        n.to_string(),
                        t,
                        *id,
                    )],
                    subtype_relation: BTreeSet::new(),
                },
            }
        }
        Expr::Declaration(_) => construct_type("()").into(),
        Expr::Call(f, a) => {
            let f_t = min_type_incomplite(f);
            let a_t = min_type_incomplite(a);
            let b: ast1::Type = TypeUnit::new_variable().into();
            let c: ast1::Type = TypeUnit::new_variable().into();
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
            IncompleteType {
                constructor: b,
                requirements: marge_requirements(vec![
                    f_sub_cb,
                    a_sub_c,
                    f_t.requirements,
                    a_t.requirements,
                ]),
            }
        }
        Expr::Unit => construct_type("()").into(),
    }
}

fn multi_expr_min_type(exprs: &[Expr]) -> IncompleteType {
    let mut req = Requirements::default();
    let t = exprs
        .iter()
        .map(|e| {
            let t = min_type_incomplite(e);
            req = marge_requirements(vec![
                req.clone(),
                t.clone().requirements,
            ]);
            t
        })
        .collect::<Vec<_>>();
    let t = t.last().unwrap().clone();
    IncompleteType {
        constructor: t.constructor,
        requirements: req,
    }
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
) -> ((ast1::Type, ast1::Type), Requirements) {
    let body_type = multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(|p| pattern_to_type(p)).unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type =
            TypeUnit::Fn(pattern_type.clone().into(), arm_type).into()
    }
    let bindings: FxHashMap<String, ast1::Type> =
        bindings.into_iter().flatten().collect();
    let (variable_requirements, subtype_requirement): (
        Vec<_>,
        Vec<_>,
    ) = body_type
        .requirements
        .variable_requirements
        .into_iter()
        .flat_map(|p| {
            if let Some(a) = bindings.get(&p.0) {
                vec![
                    Err((a.clone(), p.1.clone())),
                    Err((p.1, a.clone())),
                ]
            } else {
                vec![Ok(p)]
            }
        })
        .partition_result();
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
    )
}

fn pattern_to_type(
    p: &Pattern,
) -> (ast1::Type, Vec<(String, ast1::Type)>) {
    match p {
        Pattern::Number(_) => (construct_type("Num"), Vec::new()),
        Pattern::StrLiteral(_) => {
            (construct_type("String"), Vec::new())
        }
        Pattern::Constructor(name, cs) => {
            let (types, bindings): (Vec<_>, Vec<_>) =
                cs.iter().map(|c| pattern_to_type(c)).unzip();
            (
                TypeUnit::Normal(name.clone(), types).into(),
                bindings.concat(),
            )
        }
        Pattern::Binder(name) => {
            let t: ast1::Type = TypeUnit::new_variable().into();
            (t.clone(), vec![(name.to_string(), t)])
        }
        Pattern::Underscore => {
            (TypeUnit::new_variable().into(), Vec::new())
        }
    }
}
