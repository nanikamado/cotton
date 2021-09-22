use crate::ast0::Pattern;
use crate::ast1::{
    Ast, Expr, FnArm, FnArmType, IncompleteType, Requirements, Type,
};
use itertools::Itertools;
use std::{collections::HashMap, vec};

pub fn type_check(ast: &Ast) {
    for d in &ast.declarations {
        eprintln!("{} :", d.identifier);
        let _ = dbg!(min_type(&d.value, &mut 0));
    }
}

fn min_type(
    expr: &Expr,
    anonymous_type_count: &mut usize,
) -> Result<IncompleteType, &'static str> {
    match expr {
        Expr::Lambda(arms) => {
            let (arm_types, requirements): (Vec<_>, Vec<_>) = arms
                .iter()
                .map(|a| arm_min_type(a, anonymous_type_count))
                .collect::<Result<Vec<_>, _>>()?
                .iter()
                .cloned()
                .unzip();
            Ok(IncompleteType {
                constructor: Type::Fn(arm_types),
                requirements: marge_requirements(requirements),
            })
        }
        Expr::Number(_) => {
            Ok(Type::Normal("Num".to_string(), Vec::new()).into())
        }
        Expr::StrLiteral(_) => {
            Ok(Type::Normal("String".to_string(), Vec::new()).into())
        }
        Expr::Identifier(n) => {
            let t = new_anonymous_type(anonymous_type_count);
            Ok(IncompleteType {
                constructor: t.clone(),
                requirements: Requirements {
                    variable_requirements: vec![(n.to_string(), t)],
                    subtype_relationship: Vec::new(),
                },
            })
        }
        Expr::Declaration(_) => {
            Ok(Type::Normal("[]".to_string(), Vec::new()).into())
        }
        Expr::Call(f, a) => {
            let f_t = min_type(f, anonymous_type_count)?;
            let a_t = min_type(a, anonymous_type_count)?;
            let b = new_anonymous_type(anonymous_type_count);
            let c = new_anonymous_type(anonymous_type_count);
            // c -> b
            let cb_fn =
                Type::Fn(vec![FnArmType(c.clone(), b.clone())]);
            // f < c -> b
            let f_sub_cb = Requirements {
                variable_requirements: Vec::new(),
                subtype_relationship: {
                    vec![(f_t.constructor, cb_fn)]
                },
            };
            // a < c
            let a_sub_c = Requirements {
                variable_requirements: Vec::new(),
                subtype_relationship: vec![(a_t.constructor, c)],
            };
            Ok(IncompleteType {
                constructor: b,
                requirements: marge_requirements(vec![
                    f_sub_cb,
                    a_sub_c,
                    f_t.requirements,
                    a_t.requirements,
                ]),
            })
        }
        Expr::Unit => {
            Ok(Type::Normal("[]".to_string(), Vec::new()).into())
        }
    }
}

fn multi_expr_min_type(
    exprs: &[Expr],
    anonymous_type_count: &mut usize,
) -> Result<IncompleteType, &'static str> {
    let mut req = Requirements::default();
    let t = exprs
        .iter()
        .map(|e| {
            let t = min_type(e, anonymous_type_count)?;
            req = marge_requirements(vec![
                req.clone(),
                t.clone().requirements,
            ]);
            Ok(t)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(t.last().unwrap().clone())
}

fn new_anonymous_type(anonymous_type_count: &mut usize) -> Type {
    *anonymous_type_count += 1;
    Type::Anonymous(*anonymous_type_count - 1)
}

fn marge_requirements(
    requirements: Vec<Requirements>,
) -> Requirements {
    let mut rst = Requirements::default();
    for mut r in requirements {
        rst.variable_requirements
            .append(&mut r.variable_requirements);
        rst.subtype_relationship.append(&mut r.subtype_relationship);
    }
    rst
}

fn arm_min_type(
    arm: &FnArm,
    anonymous_type_count: &mut usize,
) -> Result<(FnArmType, Requirements), &'static str> {
    let body_type =
        multi_expr_min_type(&arm.exprs, anonymous_type_count)?;
    let (types, bindings): (Vec<_>, Vec<_>) = arm
        .pattern
        .iter()
        .map(|p| pattern_to_type(p, anonymous_type_count))
        .unzip();
    let mut arm_type = body_type.constructor;
    for pattern_type in types[1..].iter().rev() {
        arm_type =
            Type::Fn(vec![FnArmType(pattern_type.clone(), arm_type)])
    }
    let arm_type = FnArmType(types[0].clone(), arm_type);
    let bindings: HashMap<String, Type> =
        bindings.into_iter().flatten().collect();
    let (variable_requirements, mut subtype_requirement): (
        Vec<_>,
        Vec<_>,
    ) = body_type
        .requirements
        .variable_requirements
        .into_iter()
        .map(|p| {
            if let Some(a) = bindings.get(&p.0) {
                Err((a.clone(), p.1))
            } else {
                Ok(p)
            }
        })
        .partition_result();
    Ok((
        arm_type,
        Requirements {
            variable_requirements,
            subtype_relationship: {
                let mut tmp =
                    body_type.requirements.subtype_relationship;
                tmp.append(&mut subtype_requirement);
                tmp
            },
        },
    ))
}

fn pattern_to_type(
    p: &Pattern,
    anonymous_type_count: &mut usize,
) -> (Type, Vec<(String, Type)>) {
    match p {
        Pattern::Number(_) => {
            (Type::Normal("Num".to_string(), Vec::new()), Vec::new())
        }
        Pattern::StrLiteral(_) => (
            Type::Normal("String".to_string(), Vec::new()),
            Vec::new(),
        ),
        Pattern::Constructor(name, cs) => {
            let (types, bindings): (Vec<_>, Vec<_>) = cs
                .iter()
                .map(|c| pattern_to_type(c, anonymous_type_count))
                .unzip();
            (Type::Normal(name.clone(), types), bindings.concat())
        }
        Pattern::Binder(name) => {
            let t = new_anonymous_type(anonymous_type_count);
            (t.clone(), vec![(name.to_string(), t)])
        }
        Pattern::Underscore => {
            (new_anonymous_type(anonymous_type_count), Vec::new())
        }
    }
}
