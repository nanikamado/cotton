mod ast_step1;
mod ast_step2;
mod codegen;
pub mod intrinsics;

pub use crate::ast_step1::{
    Block, ConstructorId, Env, GlobalVariable, LocalVariable, TypeId,
    VariableDecl,
};

impl Env {
    pub fn gen_c(self, entry_point: GlobalVariable) -> String {
        let ast = self.build_ast4(entry_point);
        let ast = ast_step2::Ast::from(ast);
        codegen::codegen(ast)
    }
}
