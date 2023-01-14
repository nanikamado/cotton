use crate::ast_step1::decl_id::DeclId;
use crate::ast_step1::ident_id::IdentId;
use crate::ast_step2::types::Type;
use crate::ast_step2::{ConstructorId, TypeId};
use crate::ast_step3::VariableId;
use fxhash::FxHashMap;
use parser::token_id::TokenId;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenMapEntry {
    Decl(DeclId),
    DataDecl(DeclId),
    Ident(IdentId),
    ResolvedIdent(VariableId),
    TypeId(TypeId),
    TypeAlias,
    Constructor(ConstructorId),
    TypeVariable,
    Interface,
    KeyWord,
    VariableDeclInInterface(Type),
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct TokenMap(pub FxHashMap<TokenId, TokenMapEntry>);

impl TokenMap {
    pub fn insert(&mut self, id: Option<TokenId>, entry: TokenMapEntry) {
        if let Some(id) = id {
            self.0.insert(id, entry);
        }
    }
}
