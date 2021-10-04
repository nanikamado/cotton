use crate::ast1::{IncompleteType, Requirements, Type};
use itertools::Itertools;
use std::collections::{BTreeSet, HashSet};
use Type::{Empty, Fn, Normal, Union, Variable};

impl Type {
    pub fn all_type_variables(&self) -> HashSet<usize> {
        match self {
            Fn(a, r) => {
                let mut a = a.all_type_variables();
                a.extend(r.all_type_variables());
                a
            }
            Normal(_, cs) => cs
                .iter()
                .flat_map(|c| c.all_type_variables())
                .collect(),
            Union(cs) => cs
                .iter()
                .flat_map(|c| c.all_type_variables())
                .collect(),
            Variable(n) => [*n].iter().copied().collect(),
            Empty => HashSet::new(),
        }
    }

    pub fn replace_num(self, from: usize, to: &Self) -> Self {
        match self {
            Fn(args, rtn) => Fn(
                args.replace_num(from, to).into(),
                rtn.replace_num(from, to).into(),
            ),
            Union(m) => Type::union_from(
                m.into_iter().map(|t| t.replace_num(from, to)),
            ),
            Normal(name, cs) => {
                let cs = cs
                    .into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect_vec();
                if cs.contains(&Empty) {
                    Empty
                } else {
                    Normal(name, cs)
                }
            }
            Variable(n) => {
                if n == from {
                    to.clone()
                } else {
                    Variable(n)
                }
            }
            Empty => Empty,
        }
    }

    pub fn replace_type(self, from: &Type, to: &Type) -> Self {
        match self {
            t if t == *from => to.clone(),
           Fn(args, rtn) => Fn(
                args.replace_type(from, to).into(),
                rtn.replace_type(from, to).into(),
            ),
            Union(m) => Union(
                m.into_iter()
                    .map(|t| t.replace_type(from, to))
                    .collect(),
            ),
            Normal(name, cs) => Normal(
                name,
                cs.into_iter()
                    .map(|t| t.replace_type(from, to))
                    .collect(),
            ),
            Variable(n) => Variable(n),
            Empty => Empty,
        }
    }

    pub fn is_singleton(&self) -> bool {
        match self {
            Normal(_, cs) => {
                cs.iter().all(|c| c.is_singleton())
            }
            Fn(a, b) => a.is_singleton() && b.is_singleton(),
            _ => false,
        }
    }

    pub fn union_with(self, other: Type) -> Type {
        match (self, other) {
            (Union(mut a), Union(b)) => {
                a.extend(b);
                Union(a)
            }
            (Union(mut a), b) | (b, Union(mut a)) => {
                a.insert(b);
                Union(a)
            }
            (a, b) => Union(vec![a, b].into_iter().collect()),
        }
    }

    pub fn union_from(it: impl Iterator<Item = Type>) -> Self {
        let mut u = BTreeSet::new();
        for t in it {
            match t {
                Union(a) => u.extend(a),
                Empty => (),
                other => {
                    u.insert(other);
                }
            }
        }
        Union(u)
    }

    #[allow(unused)]
    pub fn contains(&self, variable_num: usize) -> bool {
        match self {
            Normal(_, cs) => {
                cs.iter().any(|c| c.contains(variable_num))
            }
            Fn(a, r) => {
                a.contains(variable_num) || r.contains(variable_num)
            }
            Union(cs) => {
                cs.iter().any(|cs| cs.contains(variable_num))
            }
            Variable(n) => *n == variable_num,
            Empty => false,
        }
    }
}

impl IncompleteType {
    fn all_type_variables(&self) -> HashSet<usize> {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation,
                },
        } = self;
        variable_requirements
            .iter()
            .flat_map(|(_, t)| t.all_type_variables())
            .chain(subtype_relation.iter().flat_map(|(a, b)| {
                let mut a = a.all_type_variables();
                a.extend(b.all_type_variables());
                a
            }))
            .chain(constructor.all_type_variables())
            .collect()
    }

    pub fn change_variable_num(mut self) -> Self {
        let anos = self.all_type_variables();
        for a in anos {
            self = self.replace_num(a, &Type::new_variable())
        }
        self
    }

    pub fn replace_num(self, from: usize, to: &Type) -> Self {
        let IncompleteType {
            constructor,
            requirements:
                Requirements {
                    variable_requirements,
                    subtype_relation: subtype_relationship,
                },
        } = self;
        IncompleteType {
            constructor: constructor.replace_num(from, to),
            requirements: Requirements {
                variable_requirements: variable_requirements
                    .into_iter()
                    .map(|(name, t)| (name, t.replace_num(from, to)))
                    .collect(),
                subtype_relation: subtype_relationship
                    .into_iter()
                    .map(|(a, b)| {
                        (
                            a.replace_num(from, to),
                            b.replace_num(from, to),
                        )
                    })
                    .collect(),
            },
        }
    }
}

impl Requirements {
    pub fn merge(self, other: Self) -> Self {
        Self {
            variable_requirements: [
                self.variable_requirements,
                other.variable_requirements,
            ]
            .concat(),
            subtype_relation: {
                let mut s = self.subtype_relation;
                s.extend(other.subtype_relation);
                s
            },
        }
    }
}
