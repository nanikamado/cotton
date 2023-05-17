use std::fmt::{Debug, Display};

#[derive(Debug, PartialEq, Hash, Clone, Copy, Eq)]
pub struct LocalVariable(usize);

#[derive(Debug, PartialEq)]
pub struct LocalVariableCollector<T>(Vec<T>);

impl<T> LocalVariableCollector<T> {
    pub fn new_variable(&mut self, t: T) -> LocalVariable {
        self.0.push(t);
        LocalVariable(self.0.len() - 1)
    }
}

impl<T> LocalVariableCollector<T> {
    pub fn new() -> Self {
        LocalVariableCollector(Vec::new())
    }

    pub fn get_type(&self, i: LocalVariable) -> &T {
        &self.0[i.0]
    }

    pub fn map<U>(self, f: impl FnMut(T) -> U) -> LocalVariableCollector<U> {
        LocalVariableCollector(self.0.into_iter().map(f).collect())
    }
}

impl Display for LocalVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
