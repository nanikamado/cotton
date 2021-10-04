mod intrinsics;
mod simplify;
mod type_util;

use crate::ast0::{DataDeclaration, Pattern};
use crate::ast1::{
    Ast, Expr, FnArm, IncompleteType, Requirements, Type,
};
use intrinsics::INTRINSIC_VARIABLES;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::{collections::HashMap, vec};

pub fn type_check(ast: &Ast) {
    let mut toplevels: HashMap<String, Vec<Toplevel>> =
        HashMap::new();
    for (name, ts) in &*INTRINSIC_VARIABLES {
        *toplevels.entry(name.clone()).or_default() = ts
            .iter()
            .map(|t| Toplevel {
                incomplete: t.clone().into(),
                face: None,
            })
            .collect();
    }
    for d in &ast.data_declarations {
        let d_type = constructor_type(d.clone());
        toplevels.entry(d.name.clone()).or_default().push(Toplevel {
            incomplete: d_type.into(),
            face: None,
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
            },
        );
    }
    for (name, top) in &toplevels {
        eprintln!("{} : ", name);
        for t in top {
            if let Some(f) = &t.face {
                eprintln!("face: {}", f);
                eprintln!("incomplete: {}", t.incomplete);
            } else {
                eprintln!("{}", t.incomplete);
            }
        }
    }
    let toplevels = test_simplify(toplevels);
    eprintln!("------------------------------");
    for (name, top) in toplevels {
        eprintln!("{} : ", name);
        for t in top {
            eprintln!("{}", t.incomplete);
        }
    }
}

struct Toplevel {
    incomplete: IncompleteType,
    face: Option<IncompleteType>,
}

fn test_simplify(
    mut toplevels: HashMap<String, Vec<Toplevel>>,
) -> HashMap<String, Vec<Toplevel>> {
    loop {
        // (name, num, variable req num, type)
        let mut resolved: Option<(&String, usize, IncompleteType)> =
            None;
        'outer: for (name, types) in &toplevels {
            for (t_index, t) in types.iter().enumerate() {
                if !t.incomplete.resolved() {
                    for (req_i, (req_name, req_t)) in t
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
                        }) {
                            continue;
                        }
                        let successes: Vec<_> = candidates
                            .iter()
                            .filter_map(|cand| {
                                let cand_t =
                                    if let Some(face) = &cand.face {
                                        face
                                    } else {
                                        &cand.incomplete
                                    };
                                let cand_t = cand_t
                                    .clone()
                                    .change_variable_num();
                                let cand_resolved = cand_t.resolved();
                                let mut incomplete =
                                    t.incomplete.clone();
                                incomplete
                                    .requirements
                                    .variable_requirements
                                    .remove(req_i);
                                incomplete
                                    .requirements
                                    .subtype_relation
                                    .insert((
                                        cand_t.constructor,
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
                                    .map(|t| (t, cand_resolved))
                            })
                            .collect();
                        if successes.len() == 1 && successes[0].1 {
                            resolved = Some((
                                name,
                                t_index,
                                successes[0].0.clone(),
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
        if let Some((name, v_index, r)) = resolved {
            let name = name.clone();
            toplevels.get_mut(&name).unwrap()[v_index].incomplete = r;
        } else {
            break;
        }
    }
    toplevels
}

fn constructor_type(d: DataDeclaration) -> Type {
    let field_types: Vec<_> =
        (0..d.field_len).map(|_| Type::new_variable()).collect();
    let mut t = Type::Normal(d.name, field_types.clone());
    for field in field_types.into_iter().rev() {
        t = Type::Fn(Box::new(field), Box::new(t))
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
            let (args, rtns): (Vec<Type>, Vec<Type>) =
                arm_types.into_iter().unzip();
            let constructor = if args.len() == 1 {
                Type::Fn(
                    Box::new(args.into_iter().next().unwrap()),
                    Box::new(rtns.into_iter().next().unwrap()),
                )
            } else {
                Type::Fn(
                    Box::new(Type::union_from(args.into_iter())),
                    Box::new(Type::union_from(rtns.into_iter())),
                )
            };
            IncompleteType {
                constructor,
                requirements: marge_requirements(requirements),
            }
        }
        Expr::Number(_) => {
            Type::Normal("Num".to_string(), Vec::new()).into()
        }
        Expr::StrLiteral(_) => {
            Type::Normal("String".to_string(), Vec::new()).into()
        }
        Expr::Identifier(n) => {
            let t = Type::new_variable();
            IncompleteType {
                constructor: t.clone(),
                requirements: Requirements {
                    variable_requirements: vec![(n.to_string(), t)],
                    subtype_relation: BTreeSet::new(),
                },
            }
        }
        Expr::Declaration(_) => {
            Type::Normal("()".to_string(), Vec::new()).into()
        }
        Expr::Call(f, a) => {
            let f_t = min_type_incomplite(f);
            let a_t = min_type_incomplite(a);
            let b = Type::new_variable();
            let c = Type::new_variable();
            // c -> b
            let cb_fn =
                Type::Fn(Box::new(c.clone()), Box::new(b.clone()));
            // f < c -> b
            let f_sub_cb = Requirements {
                variable_requirements: Vec::new(),
                subtype_relation: {
                    [(f_t.constructor, cb_fn)]
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
        Expr::Unit => {
            Type::Normal("()".to_string(), Vec::new()).into()
        }
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

fn arm_min_type(arm: &FnArm) -> ((Type, Type), Requirements) {
    let body_type = multi_expr_min_type(&arm.exprs);
    let (types, bindings): (Vec<_>, Vec<_>) =
        arm.pattern.iter().map(|p| pattern_to_type(p)).unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type = Type::Fn(
            Box::new(pattern_type.clone()),
            Box::new(arm_type),
        )
    }
    let bindings: HashMap<String, Type> =
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

fn pattern_to_type(p: &Pattern) -> (Type, Vec<(String, Type)>) {
    match p {
        Pattern::Number(_) => {
            (Type::Normal("Num".to_string(), Vec::new()), Vec::new())
        }
        Pattern::StrLiteral(_) => (
            Type::Normal("String".to_string(), Vec::new()),
            Vec::new(),
        ),
        Pattern::Constructor(name, cs) => {
            let (types, bindings): (Vec<_>, Vec<_>) =
                cs.iter().map(|c| pattern_to_type(c)).unzip();
            (Type::Normal(name.clone(), types), bindings.concat())
        }
        Pattern::Binder(name) => {
            let t = Type::new_variable();
            (t.clone(), vec![(name.to_string(), t)])
        }
        Pattern::Underscore => (Type::new_variable(), Vec::new()),
    }
}
