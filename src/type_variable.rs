use crate::ast1::TypeUnit;
use std::cell::Cell;

impl TypeUnit {
    pub fn new_variable() -> Self {
        Self::Variable(Self::new_variable_num())
    }

    pub fn new_variable_num() -> usize {
        VARIABLE_COUNT.with(|c| {
            let t = c.get();
            c.set(t + 1);
            t
        })
    }
}

thread_local! {
    static VARIABLE_COUNT: Cell<usize> = Cell::new(0);
}
