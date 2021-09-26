mod intrinsics;
mod simplify;

use crate::ast0::{DataDeclaration, Pattern};
use crate::ast1::{
    Ast, Expr, FnArm, FnArmType, IncompleteType, Requirements, Type,
};
use intrinsics::INTRINSIC_VARIABLES;
use itertools::Itertools;
use std::fmt::Display;
use std::{collections::HashMap, vec};

pub fn type_check(ast: &Ast) {
    use simplify::simplify_type;
    let mut resolved_variables: HashMap<String, Vec<simplify::Type>> =
        INTRINSIC_VARIABLES.clone();
    let mut variable_count: HashMap<String, usize> =
        INTRINSIC_VARIABLES
            .iter()
            .map(|(name, ts)| (name.clone(), ts.len()))
            .collect();
    // let mut resolved_variables2: HashMap<
    //     String,
    //     Vec<Option<simplify::Type>>,
    // > = INTRINSIC_VARIABLES
    //     .iter()
    //     .map(|(name, ts)| {
    //         (
    //             name.clone(),
    //             ts.into_iter().map(|t| Some(t.clone())).collect(),
    //         )
    //     })
    //     .collect();
    let mut anonymous_type_count = 0;
    for d in &ast.data_declarations {
        resolved_variables.entry(d.name.clone()).or_default().push(
            constructor_type(d.clone(), &mut anonymous_type_count),
        );
        *variable_count.entry(d.name.clone()).or_default() += 1;
    }
    let mut unresolved_variables = ast
        .declarations
        .iter()
        .map(|d| {
            *variable_count
                .entry(d.identifier.clone())
                .or_default() += 1;
            (
                d.identifier.clone(),
                min_type(&d.value, &mut anonymous_type_count)
                    .unwrap()
                    .into(),
            )
        })
        .collect_vec();
    loop {
        eprintln!("-------------------");
        let resolved = resolved_variables.clone();
        let declar_types_last = unresolved_variables.clone();
        unresolved_variables = unresolved_variables
            .into_iter()
            .filter_map(
                |(name, t): (String, simplify::IncompleteType)| {
                    eprint!("{} : ", name);
                    let t = simplify_type(
                        t.clone(),
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
                        &mut anonymous_type_count,
                    );
                    eprintln!("{}", t);
                    if t.resolved() {
                        resolved_variables
                            .entry(name.clone())
                            .or_default()
                            .push(t.constructor.clone());
                        None
                    } else {
                        Some((name, t))
                    }
                },
            )
            .collect();
        if declar_types_last == unresolved_variables {
            break;
        }
    }
    eprintln!("-- resolved --");
    for (name, rs) in resolved_variables {
        eprintln!("{} :", name);
        for r in rs {
            eprintln!("{}", r);
        }
    }
}

fn constructor_type(
    d: DataDeclaration,
    anonymous_type_count: &mut usize,
) -> simplify::Type {
    use simplify::Type;
    let field_types: Vec<_> = (0..d.field_len)
        .map(|_| new_anonymous_type(anonymous_type_count).into())
        .collect();
    let mut t = Type::Normal(d.name, field_types.clone());
    for field in field_types.into_iter().rev() {
        t = Type::Fn(Box::new(field), Box::new(t))
    }
    t
}

fn min_type(
    expr: &Expr,
    anonymous_type_count: &mut usize,
) -> Result<IncompleteType, &'static str> {
    Ok(min_type_incomplite(expr, anonymous_type_count))
}

fn min_type_incomplite(
    expr: &Expr,
    anonymous_type_count: &mut usize,
) -> IncompleteType {
    match expr {
        Expr::Lambda(arms) => {
            let (arm_types, requirements): (Vec<_>, Vec<_>) = arms
                .iter()
                .map(|a| arm_min_type(a, anonymous_type_count))
                .unzip();
            IncompleteType {
                constructor: Type::Fn(arm_types),
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
            let t = new_anonymous_type(anonymous_type_count);
            IncompleteType {
                constructor: t.clone(),
                requirements: Requirements {
                    variable_requirements: vec![(n.to_string(), t)],
                    subtype_relationship: Vec::new(),
                },
            }
        }
        Expr::Declaration(_) => {
            Type::Normal("()".to_string(), Vec::new()).into()
        }
        Expr::Call(f, a) => {
            let f_t = min_type_incomplite(f, anonymous_type_count);
            let a_t = min_type_incomplite(a, anonymous_type_count);
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

#[allow(dead_code)]
fn all_anonymous_types_in(t: Type) -> Vec<usize> {
    match t {
        Type::Normal(_, _) => Vec::new(),
        Type::Fn(arms) => {
            let mut rst = Vec::new();
            for FnArmType(a, b) in arms {
                rst.append(&mut all_anonymous_types_in(a));
                rst.append(&mut all_anonymous_types_in(b));
            }
            rst
        }
        Type::Union(a, b) => {
            [all_anonymous_types_in(*a), all_anonymous_types_in(*b)]
                .concat()
        }
        Type::Anonymous(a) => vec![a],
    }
}

fn multi_expr_min_type(
    exprs: &[Expr],
    anonymous_type_count: &mut usize,
) -> IncompleteType {
    let mut req = Requirements::default();
    let t = exprs
        .iter()
        .map(|e| {
            let t = min_type_incomplite(e, anonymous_type_count);
            req = marge_requirements(vec![
                req.clone(),
                t.clone().requirements,
            ]);
            t
        })
        .collect::<Vec<_>>();
    t.last().unwrap().clone()
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
) -> (FnArmType, Requirements) {
    let body_type =
        multi_expr_min_type(&arm.exprs, anonymous_type_count);
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
    )
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

impl Display for IncompleteType {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} forall\n{}--",
            self.constructor, self.requirements
        )
    }
}

impl Display for Type {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        use Type::*;
        match self {
            Normal(name, cs) => {
                if cs.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        name,
                        cs.iter()
                            .map(|c| format!("{}", c))
                            .join(", ")
                    )
                }
            }
            Fn(arms) => {
                write!(
                    f,
                    "{}",
                    arms.iter()
                        .map(|FnArmType(arg, rtn)| {
                            if let Type::Fn(_) = arg {
                                format!("({}) -> {}", arg, rtn)
                            } else {
                                format!("{} -> {}", arg, rtn)
                            }
                        })
                        .join(" & ")
                )
            }
            Union(_, _) => unimplemented!(),
            Anonymous(n) => write!(f, "t{}", n),
        }
    }
}

impl Display for Requirements {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        for (a, b) in &self.subtype_relationship {
            writeln!(f, "    {} < {},", a, b)?;
        }
        for (a, b) in &self.variable_requirements {
            writeln!(f, "    ?{} : {},", a, b)?;
        }
        Ok(())
    }
}
