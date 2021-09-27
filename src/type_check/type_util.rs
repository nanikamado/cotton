use crate::ast1::Type;
use itertools::Itertools;

impl Type {
    pub fn all_anonymous_types(&self) -> Vec<usize> {
        match self {
            Type::Fn(a, r) => {
                [a.all_anonymous_types(), r.all_anonymous_types()]
                    .concat()
            }
            Type::Normal(_, cs) => {
                cs.iter().map(|c| c.all_anonymous_types()).concat()
            }
            Type::Union(cs) => {
                cs.iter().map(|c| c.all_anonymous_types()).concat()
            }
            Type::Anonymous(n) => vec![*n],
            Type::Empty => Vec::new(),
        }
    }

    pub fn new_variable(anonymous_type_count: &mut usize) -> Type {
        *anonymous_type_count += 1;
        Type::Anonymous(*anonymous_type_count - 1)
    }

    pub fn change_anonymous_num(
        mut self,
        anonymous_type_count: &mut usize,
    ) -> Type {
        let anos = self.all_anonymous_types();
        for a in anos {
            self = self.replace_num(
                a,
                &Type::new_variable(anonymous_type_count),
            )
        }
        self
    }

    pub fn replace_num(self, from: usize, to: &Type) -> Self {
        match self {
            Type::Fn(args, rtn) => Type::Fn(
                args.replace_num(from, to).into(),
                rtn.replace_num(from, to).into(),
            ),
            Type::Union(m) => Type::Union(
                m.into_iter()
                    .map(|t| t.replace_num(from, to))
                    .collect(),
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
            Type::Empty => Type::Empty
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
            Type::Empty => false
        }
    }
}
