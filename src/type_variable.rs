use crate::ast1::Type;
use std::cell::Cell;

impl Type {
    pub fn new_variable() -> Type {
        let c = VARIABLE_COUNT.with(|c| {
            let t = c.get();
            c.set(t + 1);
            t
        });
        Type::Variable(c)
    }
}

thread_local! {
    static VARIABLE_COUNT: Cell<usize> = Cell::new(0);
}
