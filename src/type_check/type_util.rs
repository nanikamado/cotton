use crate::ast1::{IncompleteType, Requirements, Type};
use std::collections::{BTreeSet, HashSet};
use Type::*;

impl Type {
    pub fn all_anonymous_types(&self) -> HashSet<usize> {
        match self {
            Type::Fn(a, r) => {
                let mut a = a.all_anonymous_types();
                a.extend(r.all_anonymous_types());
                a
            }
            Type::Normal(_, cs) => cs
                .iter()
                .flat_map(|c| c.all_anonymous_types())
                .collect(),
            Type::Union(cs) => cs
                .iter()
                .flat_map(|c| c.all_anonymous_types())
                .collect(),
            Type::Anonymous(n) => [*n].iter().copied().collect(),
            Type::Empty => HashSet::new(),
        }
    }

    pub fn change_anonymous_num(mut self) -> Type {
        let anos = self.all_anonymous_types();
        for a in anos {
            self = self.replace_num(a, &Type::new_variable())
        }
        self
    }

    pub fn replace_num(self, from: usize, to: &Type) -> Self {
        match self {
            Type::Fn(args, rtn) => Type::Fn(
                args.replace_num(from, to).into(),
                rtn.replace_num(from, to).into(),
            ),
            Type::Union(m) => Type::union_from(
                m.into_iter().map(|t| t.replace_num(from, to)),
            ),
            Type::Normal(name, cs) => Type::Normal(
                name,
                cs.into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect(),
            ),
            Type::Anonymous(n) => {
                if n == from {
                    to.clone()
                } else {
                    Type::Anonymous(n)
                }
            }
            Type::Empty => Type::Empty,
        }
    }

    pub fn replace_type(self, from: &Type, to: &Type) -> Self {
        match self {
            t if t == *from => to.clone(),
            Type::Fn(args, rtn) => Type::Fn(
                args.replace_type(from, to).into(),
                rtn.replace_type(from, to).into(),
            ),
            Type::Union(m) => Type::Union(
                m.into_iter()
                    .map(|t| t.replace_type(from, to))
                    .collect(),
            ),
            Type::Normal(name, cs) => Type::Normal(
                name,
                cs.into_iter()
                    .map(|t| t.replace_type(from, to))
                    .collect(),
            ),
            Type::Anonymous(n) => Type::Anonymous(n),
            Type::Empty => Type::Empty,
        }
    }

    pub fn is_singleton(&self) -> bool {
        match self {
            Type::Normal(_, cs) => {
                cs.iter().all(|c| c.is_singleton())
            }
            Type::Fn(a, b) => a.is_singleton() && b.is_singleton(),
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
            Type::Normal(_, cs) => {
                cs.iter().any(|c| c.contains(variable_num))
            }
            Type::Fn(a, r) => {
                a.contains(variable_num) || r.contains(variable_num)
            }
            Type::Union(cs) => {
                cs.iter().any(|cs| cs.contains(variable_num))
            }
            Type::Anonymous(n) => *n == variable_num,
            Type::Empty => false,
        }
    }
}

impl IncompleteType {
    fn all_anonymous_types(&self) -> HashSet<usize> {
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
            .flat_map(|(_, t)| t.all_anonymous_types())
            .chain(subtype_relation.iter().flat_map(|(a, b)| {
                let mut a = a.all_anonymous_types();
                a.extend(b.all_anonymous_types());
                a
            }))
            .chain(constructor.all_anonymous_types())
            .collect()
    }

    pub fn change_anonymous_num(mut self) -> Self {
        let anos = self.all_anonymous_types();
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
