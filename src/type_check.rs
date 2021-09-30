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

type DeclId = u32;

pub fn type_check(ast: &Ast) {
    use simplify::simplify_type;
    let mut fixed_variables: HashMap<String, Vec<Type>> =
        INTRINSIC_VARIABLES.clone();
    let mut variable_count: HashMap<String, usize> =
        INTRINSIC_VARIABLES
            .iter()
            .map(|(name, ts)| (name.clone(), ts.len()))
            .collect();
    let mut decl_id = 0;
    for d in &ast.data_declarations {
        fixed_variables
            .entry(d.name.clone())
            .or_default()
            .push(constructor_type(d.clone()));
        *variable_count.entry(d.name.clone()).or_default() += 1;
        decl_id += 1;
    }
    let mut unresolved_variables = ast
        .declarations
        .iter()
        .map(|d| {
            *variable_count
                .entry(d.identifier.clone())
                .or_default() += 1;
            decl_id += 1;
            let mut t = min_type(&d.value).unwrap();
            if let Some(annotation) = &d.type_annotation {
                let annotation =
                    annotation.clone().change_anonymous_num();
                t.requirements.subtype_relation.insert((
                    t.constructor.clone(),
                    annotation.constructor.clone(),
                ));
                t.requirements.subtype_relation.insert((
                    annotation.constructor,
                    t.constructor.clone(),
                ));
                t.requirements =
                    t.requirements.merge(annotation.requirements);
                eprintln!("65 : t : {}", t);
            }
            (d.identifier.clone(), decl_id - 1, t)
        })
        .collect_vec();
    loop {
        eprintln!("-------------------");
        let resolved = fixed_variables.clone();
        let declar_types_last = unresolved_variables.clone();
        unresolved_variables = unresolved_variables
            .into_iter()
            .filter_map(
                |(name, id, t): (String, DeclId, IncompleteType)| {
                    eprint!("{} : ", name);
                    let t = simplify_type(
                        t,
                        &resolved
                            .iter()
                            .filter_map(|(n, v)| {
                                if v.len() == 1
                                    && variable_count.get(n)
                                        == Some(&1)
                                {
                                    Some((n.clone(), v[0].clone()))
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    )
                    .unwrap();
                    eprintln!("{}", t);
                    if t.resolved() {
                        fixed_variables
                            .entry(name)
                            .or_default()
                            .push(t.constructor);
                        None
                    } else {
                        Some((name, id, t))
                    }
                },
            )
            .collect();
        if declar_types_last == unresolved_variables {
            break;
        }
    }
    eprintln!("-- resolved --");
    for (name, rs) in &fixed_variables {
        eprintln!("{} :", name);
        for r in rs {
            eprintln!("{}", r);
        }
    }
    let mut toplevels: HashMap<&str, Vec<IncompleteType>> =
        HashMap::new();
    for (name, _, t) in &unresolved_variables {
        toplevels.entry(name).or_default().push(t.clone());
    }
    for (name, t) in &fixed_variables {
        toplevels.entry(name).or_default().append(
            &mut t.iter().map(|a| a.clone().into()).collect(),
        );
    }
    let mut unresolved_variables_map: HashMap<
        &str,
        Vec<(DeclId, IncompleteType)>,
    > = HashMap::new();
    for (name, id, t) in &unresolved_variables {
        unresolved_variables_map
            .entry(name)
            .or_default()
            .push((*id, t.clone()));
    }
    // for (name, id, t) in &unresolved_variables {
    //     let mut additional_sub_req: Vec<(Type, Type)> = Vec::new();
    //     let _ = t.requirements.variable_requirements.iter().map(
    //         |(req_name, req_t)| {
    //             if let Some(candi) =
    //                 unresolved_variables_map.get(&req_name[..])
    //             {
    //                 if candi.len() == 1 && candi[0].0 == *id {
    //                     additional_sub_req.push((
    //                         req_t.clone(),
    //                         t.constructor.clone(),
    //                     ));
    //                     additional_sub_req.push((
    //                         t.constructor.clone(),
    //                         req_t.clone(),
    //                     ));
    //                     false
    //                 } else {
    //                     true
    //                 }
    //             } else {
    //                 true
    //             }
    //         },
    //     );
    // }
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
    t.last().unwrap().clone()
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
