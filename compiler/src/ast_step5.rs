pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::unhashable_type::UnhashableTypeMemo;
use crate::ast_step4::{
    self, BasicFunction, GlobalVariable, LambdaId, LocalVariableTypes,
    PaddedTypeMap, ReplaceMap, TypeId, TypePointer,
};
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::{Debug, Display};
use std::iter::once;
use std::mem;

#[derive(Debug)]
pub struct Ast {
    pub variable_decls: Vec<VariableDecl>,
    pub entry_point: FxLambdaId,
    pub variable_names: FxHashMap<VariableId, String>,
    pub functions: Vec<Function>,
    pub type_map: PaddedTypeMap,
    pub variable_types: LocalVariableCollector<Type>,
    pub fx_type_map: FxHashMap<LambdaId<Type>, FxLambdaId>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct GlobalVariableId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: String,
    pub value: Block,
    pub ret: VariableId,
    pub decl_id: GlobalVariableId,
    pub t: Type,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Tag { tag: u32 },
    I64 { value: String },
    Str { value: String },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(LocalVariable, Expr),
    Test(Tester, VariableId),
    FailTest,
    ImpossibleTypeError,
    TryCatch(Block, Block),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: FxLambdaId,
        context: Vec<LocalVariable>,
    },
    I64(String),
    Str(String),
    Ident(VariableId),
    Call {
        f: VariableId,
        a: VariableId,
        real_function: FxLambdaId,
    },
    BasicCall {
        args: Vec<VariableId>,
        id: BasicFunction,
    },
    Upcast {
        tag: u32,
        value: VariableId,
    },
    Downcast {
        tag: u32,
        value: VariableId,
    },
    Ref(VariableId),
    Deref(VariableId),
}

#[derive(Debug, PartialEq, Hash, Clone, Copy, Eq)]
pub enum VariableId {
    Local(LocalVariable),
    Global(GlobalVariableId),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub id: FxLambdaId,
    pub context: Vec<LocalVariable>,
    pub parameter: LocalVariable,
    pub body: Block,
    pub ret: VariableId,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone, Hash)]
pub struct Type<R = u32> {
    pub ts: Vec<TypeUnit<R>>,
    pub recursive: bool,
    pub reference: bool,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeInner<R = u32> {
    RecursionPoint(R),
    Type(Type<R>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeUnit<R = u32> {
    Normal { id: TypeId, args: Vec<TypeInner<R>> },
    Fn(BTreeSet<LambdaId<TypeInner<R>>>, TypeInner<R>, TypeInner<R>),
}

impl From<TypeUnit> for Type {
    fn from(value: TypeUnit) -> Self {
        Type {
            ts: once(value).collect(),
            recursive: false,
            reference: false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
enum IndexOrPointer {
    Index(u32),
    Pointer(TypePointer),
}

impl Type {
    pub fn iter(&self) -> impl Iterator<Item = &TypeUnit> {
        self.ts.iter()
    }

    pub fn len(&self) -> usize {
        self.ts.len()
    }

    pub fn contains_broken_link_rec(&self, depth: u32) -> bool {
        let depth = self.recursive as u32 + depth;
        self.ts.iter().any(|t| match t {
            TypeUnit::Normal { id: _, args } => {
                args.iter().any(|a| a.contains_broken_link(depth))
            }
            TypeUnit::Fn(l, a, r) => {
                l.iter().any(|l| l.root_t.contains_broken_link(depth))
                    || a.contains_broken_link(depth)
                    || r.contains_broken_link(depth)
            }
        })
    }

    pub fn contains_broken_link(&self) -> bool {
        self.contains_broken_link_rec(0)
    }
}

impl TypeInner {
    pub fn contains_broken_link(&self, depth: u32) -> bool {
        match self {
            TypeInner::RecursionPoint(d) => *d >= depth,
            TypeInner::Type(t) => t.contains_broken_link_rec(depth),
        }
    }
}

impl Ast {
    pub fn from(ast: ast_step4::Ast) -> Self {
        let mut memo = Env::new(
            ast.variable_decls,
            ast.local_variable_types,
            ast.type_map,
        );
        memo.monomorphize_decl_rec(
            ast.entry_point,
            ast.type_of_entry_point,
            &mut Default::default(),
        );
        let mut variable_names = FxHashMap::default();
        for v in &memo.monomorphized_variables {
            variable_names
                .insert(VariableId::Global(v.decl_id), v.name.to_string());
        }
        let b = &memo.monomorphized_variables.last().unwrap().value;
        match &b.instructions[0] {
            Instruction::Assign(_, Expr::Lambda { lambda_id, context }) => {
                debug_assert!(context.is_empty());
                let entry_point = *lambda_id;
                let mut functions = Vec::new();
                let mut fx_type_map = FxHashMap::default();
                for (id, f) in memo.functions {
                    if let FunctionEntry::Function(f) = f {
                        functions.push(f.clone());
                        fx_type_map.insert(id, f.id);
                    } else {
                        panic!()
                    }
                }
                Self {
                    variable_decls: memo.monomorphized_variables,
                    entry_point,
                    functions,
                    variable_names,
                    type_map: memo.map,
                    variable_types: memo.local_variable_collector,
                    fx_type_map,
                }
            }
            _ => panic!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct FnId {
    arg_t: Type,
    ret_t: Type,
    lambda_id: LambdaId<Type>,
}

pub struct Env {
    variable_decls: FxHashMap<GlobalVariable, ast_step4::VariableDecl>,
    monomorphized_variable_map:
        FxHashMap<(GlobalVariable, Type), GlobalVariableId>,
    monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
    functions: FxHashMap<LambdaId<Type>, FunctionEntry>,
    unhashable_type_memo: UnhashableTypeMemo,
    local_variable_types_old: LocalVariableTypes,
    local_variable_replace_map:
        FxHashMap<ast_step4::LocalVariable, LocalVariable>,
    local_variable_collector: LocalVariableCollector<Type>,
    used_local_variables: FxHashSet<LocalVariable>,
    defined_local_variables: FxHashSet<LocalVariable>,
    global_variable_count: usize,
}

#[derive(Debug)]
pub enum FunctionEntry {
    Placeholder(FxLambdaId),
    Function(Function),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct FxLambdaId(pub u32);

impl Env {
    pub fn new(
        variable_decls: Vec<ast_step4::VariableDecl>,
        local_variable_types: LocalVariableTypes,
        map: PaddedTypeMap,
    ) -> Self {
        Env {
            variable_decls: variable_decls
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            monomorphized_variable_map: Default::default(),
            monomorphized_variables: Default::default(),
            map,
            functions: FxHashMap::default(),
            unhashable_type_memo: UnhashableTypeMemo::default(),
            local_variable_types_old: local_variable_types,
            local_variable_replace_map: FxHashMap::default(),
            local_variable_collector: LocalVariableCollector::new(),
            used_local_variables: Default::default(),
            defined_local_variables: Default::default(),
            global_variable_count: 0,
        }
    }

    fn monomorphize_decl_rec(
        &mut self,
        decl_id: GlobalVariable,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> GlobalVariableId {
        let p = self.map.clone_pointer(p, replace_map);
        let t = self.get_type_unhashable_with_replace_map(p);
        let decl_id_t = (decl_id, t);
        if let Some(d) = self.monomorphized_variable_map.get(&decl_id_t) {
            *d
        } else {
            let (_, t) = decl_id_t;
            let new_decl_id = GlobalVariableId(self.global_variable_count);
            self.global_variable_count += 1;
            let d = self.variable_decls.get(&decl_id).unwrap().clone();
            self.monomorphized_variable_map
                .insert((decl_id, t.clone()), new_decl_id);
            let local_variable_replace_map_tmp =
                std::mem::take(&mut self.local_variable_replace_map);
            let ht = self.get_type_for_hash_with_replace_map(p);
            let (b, _) = self.block(d.value, &ht, replace_map);
            let d = VariableDecl {
                value: b,
                decl_id: new_decl_id,
                ret: self.get_defined_variable_id(
                    ast_step4::VariableId::Local(d.ret),
                    replace_map,
                ),
                name: d.name,
                t,
            };
            self.local_variable_replace_map = local_variable_replace_map_tmp;
            self.monomorphized_variables.push(d);
            new_decl_id
        }
    }

    fn new_variable(&mut self, t: Type) -> LocalVariable {
        let v = self.local_variable_collector.new_variable(t);
        self.defined_local_variables.insert(v);
        v
    }

    fn local_variable_def_replace(
        &mut self,
        v: ast_step4::LocalVariable,
        replace_map: &mut ReplaceMap,
    ) -> LocalVariable {
        debug_assert!(!self.local_variable_replace_map.contains_key(&v));
        let t = self.local_variable_types_old.get(v);
        let t = self.map.clone_pointer(t, replace_map);
        let t = self.get_type_unhashable_with_replace_map(t);
        let new_v = self.new_variable(t);
        self.local_variable_replace_map.insert(v, new_v);
        new_v
    }

    fn get_defined_local_variable(
        &mut self,
        v: ast_step4::LocalVariable,
        replace_map: &mut ReplaceMap,
    ) -> VariableId {
        if let Some(d) = self.local_variable_replace_map.get(&v) {
            self.used_local_variables.insert(*d);
            VariableId::Local(*d)
        } else {
            // Some variables are undefined because of
            // the elimination of unreachable code.
            let t = self.local_variable_types_old.get(v);
            let t = self.map.clone_pointer(t, replace_map);
            let t = self.get_type_unhashable_with_replace_map(t);
            let new_v = self.local_variable_collector.new_variable(t);
            VariableId::Local(new_v)
        }
    }

    fn get_defined_variable_id(
        &mut self,
        v: ast_step4::VariableId,
        replace_map: &mut ReplaceMap,
    ) -> VariableId {
        match v {
            ast_step4::VariableId::Local(d) => {
                self.get_defined_local_variable(d, replace_map)
            }
            ast_step4::VariableId::Global(d, r, p) => {
                let mut r = replace_map.clone().merge(r, &mut self.map);
                VariableId::Global(self.monomorphize_decl_rec(d, p, &mut r))
            }
        }
    }

    fn block(
        &mut self,
        block: ast_step4::Block,
        root_t: &Type,
        replace_map: &mut ReplaceMap,
    ) -> (Block, bool) {
        let mut instructions = Vec::new();
        let mut unreachable_block = false;
        for i in block.instructions {
            if self.instruction(i, root_t, replace_map, &mut instructions) {
                unreachable_block = true;
                break;
            }
        }
        (Block { instructions }, unreachable_block)
    }

    // Returns true if the block is unreachable
    fn instruction(
        &mut self,
        instruction: ast_step4::Instruction,
        root_t: &Type,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
    ) -> bool {
        match instruction {
            ast_step4::Instruction::Assign(v, e) => {
                let t = self.map.clone_pointer(
                    self.local_variable_types_old.get(v),
                    replace_map,
                );
                let e = self.expr(e, t, root_t, replace_map, instructions);
                match e {
                    Some(e) => {
                        let t = self.get_type_unhashable_with_replace_map(t);
                        let new_v = if let Some(v) =
                            self.local_variable_replace_map.get(&v)
                        {
                            *v
                        } else {
                            let new_v = self.new_variable(t);
                            self.local_variable_replace_map.insert(v, new_v);
                            new_v
                        };
                        instructions.push(Instruction::Assign(new_v, e));
                        false
                    }
                    None => {
                        instructions.push(Instruction::ImpossibleTypeError);
                        true
                    }
                }
            }
            ast_step4::Instruction::Test(
                ast_step4::Tester::I64 { value },
                a,
            ) => {
                let type_id = TypeId::Intrinsic(IntrinsicType::I64);
                let a = self.downcast(a, type_id, replace_map, instructions);
                match a {
                    Some(a) => instructions
                        .push(Instruction::Test(Tester::I64 { value }, a)),
                    None => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step4::Instruction::Test(
                ast_step4::Tester::Str { value },
                a,
            ) => {
                let type_id = TypeId::Intrinsic(IntrinsicType::String);
                let a = self.downcast(a, type_id, replace_map, instructions);
                match a {
                    Some(a) => instructions
                        .push(Instruction::Test(Tester::Str { value }, a)),
                    None => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step4::Instruction::Test(
                ast_step4::Tester::Constructor { id },
                a,
            ) => {
                let t = self.map.clone_pointer(
                    self.local_variable_types_old.get(a),
                    replace_map,
                );
                let t = self.get_type_unhashable_with_replace_map(t);
                let a = self.get_defined_local_variable(a, replace_map);
                match get_tag_normal(&t, id) {
                    GetTagNormalResult::Tagged(tag, _untagged_t) => {
                        let a = self.deref(a, &t, instructions);
                        instructions
                            .push(Instruction::Test(Tester::Tag { tag }, a));
                    }
                    GetTagNormalResult::NotTagged => (),
                    GetTagNormalResult::Impossible => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step4::Instruction::TryCatch(b1, b2) => {
                let (b1, u1) = self.block(b1, root_t, replace_map);
                let (b2, u2) = self.block(b2, root_t, replace_map);
                instructions.push(Instruction::TryCatch(b1, b2));
                u1 && u2
            }
        }
    }

    fn downcast(
        &mut self,
        a: ast_step4::LocalVariable,
        type_id: TypeId,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
    ) -> Option<VariableId> {
        let t = self
            .map
            .clone_pointer(self.local_variable_types_old.get(a), replace_map);
        let t = self.get_type_unhashable_with_replace_map(t);
        let a = self.get_defined_local_variable(a, replace_map);
        let a = self.deref(a, &t, instructions);
        match get_tag_normal(&t, type_id) {
            GetTagNormalResult::Tagged(tag, casted_t) => {
                Some(self.expr_to_variable(
                    Expr::Downcast { tag, value: a },
                    casted_t.into(),
                    instructions,
                ))
            }
            GetTagNormalResult::NotTagged => Some(a),
            GetTagNormalResult::Impossible => None,
        }
    }

    // Returns `None` if impossible type error
    fn expr(
        &mut self,
        e: ast_step4::Expr,
        p: TypePointer,
        root_t: &Type,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
    ) -> Option<Expr> {
        use Expr::*;
        let p = self.map.clone_pointer(p, replace_map);
        let t = self.get_type_unhashable_with_replace_map(p);
        let e = match e {
            ast_step4::Expr::Lambda {
                lambda_id,
                parameter,
                body,
                ret,
            } => {
                let used_local_variables_tmp =
                    mem::take(&mut self.used_local_variables);
                let defined_local_variables_tmp =
                    mem::take(&mut self.defined_local_variables);
                let possible_functions = self.get_possible_functions(p);
                let new_parameter =
                    self.local_variable_def_replace(parameter, replace_map);
                let (b, _) = self.block(body, root_t, replace_map);
                let ret = self.get_defined_variable_id(
                    ast_step4::VariableId::Local(ret),
                    replace_map,
                );
                let context = self
                    .used_local_variables
                    .iter()
                    .copied()
                    .filter(|v| !self.defined_local_variables.contains(v))
                    .collect_vec();
                let f = Function {
                    parameter: new_parameter,
                    body: b,
                    id: FxLambdaId(0),
                    context: context.clone(),
                    ret,
                };
                self.used_local_variables.extend(used_local_variables_tmp);
                self.defined_local_variables
                    .extend(defined_local_variables_tmp);
                let lambda_id = LambdaId {
                    id: lambda_id.id,
                    root_t: root_t.clone(),
                };
                let e = self.functions.get_mut(&lambda_id).unwrap();
                let FunctionEntry::Placeholder(fx_lambda_id) = *e else {
                    panic!()
                };
                *e = FunctionEntry::Function(Function {
                    id: fx_lambda_id,
                    ..f
                });
                if possible_functions.len() == 1 {
                    Lambda {
                        context,
                        lambda_id: possible_functions[0].0,
                    }
                } else {
                    let tag = possible_functions
                        .binary_search_by_key(&fx_lambda_id, |(l, _)| *l)
                        .unwrap();
                    let d =
                        self.new_variable(possible_functions[tag].1.clone());
                    instructions.push(Instruction::Assign(
                        d,
                        Lambda {
                            context,
                            lambda_id: fx_lambda_id,
                        },
                    ));
                    Upcast {
                        tag: tag as u32,
                        value: VariableId::Local(d),
                    }
                }
            }
            ast_step4::Expr::I64(s) => I64(s),
            ast_step4::Expr::Str(s) => Str(s),
            ast_step4::Expr::Ident(v) => {
                Ident(self.get_defined_variable_id(v, replace_map))
            }
            ast_step4::Expr::Call { f, a } => {
                let f_t = self.local_variable_types_old.get(f);
                let f_t = self.map.clone_pointer(f_t, replace_map);
                let possible_functions = self.get_possible_functions(f_t);
                let f = self.get_defined_local_variable(f, replace_map);
                let a = self.get_defined_local_variable(a, replace_map);
                if possible_functions.is_empty() {
                    instructions.push(Instruction::ImpossibleTypeError);
                    return None;
                }
                if possible_functions.len() == 1 {
                    Call {
                        f,
                        a,
                        real_function: possible_functions[0].0,
                    }
                } else {
                    let ret_v = self.new_variable(t);
                    let mut b = vec![Instruction::ImpossibleTypeError];
                    for (tag, (id, casted_t)) in
                        possible_functions.into_iter().enumerate()
                    {
                        let mut b2 = vec![Instruction::Test(
                            Tester::Tag { tag: tag as u32 },
                            f,
                        )];
                        let new_f = self.new_variable(casted_t);
                        b2.push(Instruction::Assign(
                            new_f,
                            Expr::Downcast {
                                tag: tag as u32,
                                value: f,
                            },
                        ));
                        b2.push(Instruction::Assign(
                            ret_v,
                            Expr::Call {
                                f: VariableId::Local(new_f),
                                a,
                                real_function: id,
                            },
                        ));
                        b = vec![Instruction::TryCatch(
                            Block { instructions: b2 },
                            Block { instructions: b },
                        )];
                    }
                    instructions.append(&mut b);
                    Ident(VariableId::Local(ret_v))
                }
            }
            ast_step4::Expr::BasicCall {
                args,
                id: BasicFunction::Construction(id),
            } => {
                let args = args
                    .into_iter()
                    .map(|a| self.get_defined_local_variable(a, replace_map))
                    .collect();
                self.add_tags_to_expr(
                    BasicCall {
                        args,
                        id: BasicFunction::Construction(id),
                    },
                    &t,
                    TypeId::UserDefined(id),
                    instructions,
                )
            }
            ast_step4::Expr::BasicCall {
                args,
                id: BasicFunction::IntrinsicConstruction(id),
            } => {
                debug_assert!(args.is_empty());
                self.add_tags_to_expr(
                    BasicCall {
                        args: Vec::new(),
                        id: BasicFunction::IntrinsicConstruction(id),
                    },
                    &t,
                    TypeId::Intrinsic(id.into()),
                    instructions,
                )
            }
            ast_step4::Expr::BasicCall {
                args,
                id:
                    id @ BasicFunction::FieldAccessor {
                        constructor,
                        field: _,
                    },
            } => {
                debug_assert_eq!(args.len(), 1);
                let a = args.into_iter().next().unwrap();
                let a = self.downcast(
                    a,
                    TypeId::UserDefined(constructor),
                    replace_map,
                    instructions,
                )?;
                BasicCall { args: vec![a], id }
            }
            ast_step4::Expr::BasicCall {
                args,
                id: BasicFunction::Intrinsic(id),
            } => {
                let rt = id.runtime_return_type();
                let arg_ts = id.runtime_arg_type_id();
                assert_eq!(t, rt);
                let args = args
                    .into_iter()
                    .zip_eq(arg_ts)
                    .map(|(a, param_t)| {
                        self.downcast(a, param_t, replace_map, instructions)
                    })
                    .collect::<Option<_>>()?;
                BasicCall {
                    args,
                    id: BasicFunction::Intrinsic(id),
                }
            }
        };
        Some(e)
    }

    fn get_possible_functions(
        &mut self,
        p: TypePointer,
    ) -> Vec<(FxLambdaId, Type)> {
        let n_len = match self.map.dereference_without_find(p) {
            ast_step4::Terminal::TypeMap(t) => t.normals.len(),
            ast_step4::Terminal::LambdaId(_) => panic!(),
        };
        assert_eq!(n_len, 1);
        let (arg_t, ret_t, fn_id) = self.map.get_fn(p);
        self.map
            .get_lambda_id_with_replace_map(fn_id)
            .clone()
            .into_iter()
            .map(|id| {
                let len = self.functions.len() as u32;
                let id_t =
                    id.map_type(|t| self.get_type_for_hash_with_replace_map(t));
                let e = self
                    .functions
                    .entry(id_t.clone())
                    .or_insert(FunctionEntry::Placeholder(FxLambdaId(len)));
                let id = match e {
                    FunctionEntry::Placeholder(id) => *id,
                    FunctionEntry::Function(f) => f.id,
                };
                (
                    id,
                    Type::from(TypeUnit::Fn(
                        [id_t.map_type(TypeInner::Type)].into(),
                        TypeInner::Type(
                            self.get_type_unhashable_with_replace_map(arg_t),
                        ),
                        TypeInner::Type(
                            self.get_type_unhashable_with_replace_map(ret_t),
                        ),
                    )),
                )
            })
            .collect()
    }

    fn get_type_unhashable_with_replace_map(&mut self, p: TypePointer) -> Type {
        self.unhashable_type_memo
            .get_type_for_hash(p, &mut self.map, false)
    }

    fn get_type_for_hash_with_replace_map(&mut self, p: TypePointer) -> Type {
        self.unhashable_type_memo
            .get_type_for_hash(p, &mut self.map, true)
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: Type,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        let d = self.new_variable(t);
        instructions.push(Instruction::Assign(d, e));
        VariableId::Local(d)
    }

    fn deref(
        &mut self,
        v: VariableId,
        t: &Type,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        if t.reference {
            debug_assert!(t.recursive);
            let d = self.new_variable(Type {
                ts: t.ts.clone(),
                recursive: true,
                reference: false,
            });
            instructions.push(Instruction::Assign(d, Expr::Deref(v)));
            VariableId::Local(d)
        } else {
            v
        }
    }

    fn add_tags_to_expr(
        &mut self,
        e: Expr,
        t: &Type,
        id: TypeId,
        instructions: &mut Vec<Instruction>,
    ) -> Expr {
        let e = match get_tag_normal(t, id) {
            GetTagNormalResult::Tagged(tag, tu) => {
                let d = self.new_variable(tu.into());
                instructions.push(Instruction::Assign(d, e));
                Expr::Upcast {
                    tag,
                    value: VariableId::Local(d),
                }
            }
            GetTagNormalResult::NotTagged => e,
            GetTagNormalResult::Impossible => {
                panic!()
            }
        };
        if t.reference {
            debug_assert!(t.recursive);
            let d = self.new_variable(Type {
                ts: t.ts.clone(),
                recursive: true,
                reference: false,
            });
            instructions.push(Instruction::Assign(d, e));
            Expr::Ref(VariableId::Local(d))
        } else {
            e
        }
    }
}

enum GetTagNormalResult {
    NotTagged,
    Impossible,
    Tagged(u32, TypeUnit),
}

fn get_tag_normal(ot: &Type, type_id: TypeId) -> GetTagNormalResult {
    debug_assert_ne!(type_id, TypeId::Intrinsic(IntrinsicType::Fn));
    let mut tag = 0;
    if ot.len() == 1 {
        let t = ot.ts.first().unwrap();
        match t {
            TypeUnit::Normal { id, .. } => {
                return if *id == type_id {
                    GetTagNormalResult::NotTagged
                } else {
                    GetTagNormalResult::Impossible
                };
            }
            TypeUnit::Fn(_, _, _) => panic!(),
        }
    }
    for t in &ot.ts {
        match t {
            TypeUnit::Normal { id, args } if *id == type_id => {
                let t = if ot.recursive {
                    TypeUnit::Normal {
                        id: *id,
                        args: args
                            .iter()
                            .map(|a| a.clone().replace_index(ot, 0))
                            .collect(),
                    }
                } else {
                    t.clone()
                };
                return GetTagNormalResult::Tagged(tag, t);
            }
            TypeUnit::Fn(lambda_ids, _, _) => {
                tag += lambda_ids.len() as u32;
            }
            _ => {
                tag += 1;
            }
        }
    }
    GetTagNormalResult::Impossible
}

impl TypeInner {
    pub fn replace_index(self, to: &Type, depth: u32) -> Self {
        debug_assert!(to.reference);
        match self {
            TypeInner::RecursionPoint(a) if a == depth => {
                TypeInner::Type(to.clone())
            }
            TypeInner::RecursionPoint(a) => TypeInner::RecursionPoint(a),
            TypeInner::Type(Type {
                ts,
                recursive,
                reference,
            }) => TypeInner::Type(Type {
                ts: ts
                    .into_iter()
                    .map(|t| t.replace_index(to, depth + recursive as u32))
                    .collect(),
                recursive,
                reference,
            }),
        }
    }
}

impl TypeUnit {
    pub fn replace_index(self, to: &Type, depth: u32) -> Self {
        debug_assert!(to.reference);
        match self {
            TypeUnit::Normal { id, args } => TypeUnit::Normal {
                id,
                args: args
                    .into_iter()
                    .map(|t| t.replace_index(to, depth))
                    .collect(),
            },
            TypeUnit::Fn(ids, a, b) => TypeUnit::Fn(
                ids,
                a.replace_index(to, depth),
                b.replace_index(to, depth),
            ),
        }
    }
}

impl Display for FxLambdaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f_{}", self.0)
    }
}

mod unhashable_type {
    use super::{IndexOrPointer, LambdaId};
    use crate::ast_step4::{PaddedTypeMap, Terminal, TypeId, TypePointer};
    use crate::ast_step5::{Type, TypeInner, TypeUnit};
    use crate::intrinsics::IntrinsicType;
    use fxhash::{FxHashMap, FxHashSet};
    use std::collections::BTreeSet;

    #[derive(Debug, Default)]
    pub struct UnhashableTypeMemo {
        type_memo: FxHashMap<TypePointer, TypeInner<IndexOrPointer>>,
        type_memo_for_hash: FxHashMap<TypePointer, TypeInner<IndexOrPointer>>,
    }

    fn remove_pointer_from_type_inner(
        t: TypeInner<IndexOrPointer>,
    ) -> TypeInner {
        match t {
            TypeInner::RecursionPoint(IndexOrPointer::Pointer(_)) => {
                panic!()
            }
            TypeInner::RecursionPoint(IndexOrPointer::Index(d)) => {
                TypeInner::RecursionPoint(d)
            }
            TypeInner::Type(Type {
                ts,
                recursive,
                reference,
            }) => TypeInner::Type(Type {
                ts: ts.into_iter().map(remove_pointer_from_type_unit).collect(),
                recursive,
                reference,
            }),
        }
    }

    fn remove_pointer_from_type_unit(t: TypeUnit<IndexOrPointer>) -> TypeUnit {
        match t {
            TypeUnit::Normal { id, args } => TypeUnit::Normal {
                id,
                args: args
                    .into_iter()
                    .map(remove_pointer_from_type_inner)
                    .collect(),
            },
            TypeUnit::Fn(id, a, b) => TypeUnit::Fn(
                id.into_iter()
                    .map(|l| l.map_type(remove_pointer_from_type_inner))
                    .collect(),
                remove_pointer_from_type_inner(a),
                remove_pointer_from_type_inner(b),
            ),
        }
    }

    impl UnhashableTypeMemo {
        pub fn get_type_for_hash(
            &mut self,
            p: TypePointer,
            map: &mut PaddedTypeMap,
            for_hash: bool,
        ) -> Type {
            let t = self.get_type_inner_for_hash(
                p,
                &Default::default(),
                map,
                for_hash,
            );
            match remove_pointer_from_type_inner(t) {
                TypeInner::RecursionPoint(_) => panic!(),
                TypeInner::Type(t) => {
                    debug_assert!(!t.contains_broken_link());
                    t
                }
            }
        }

        fn get_lambda_ids(
            &mut self,
            p: TypePointer,
            trace: &FxHashSet<TypePointer>,
            map: &mut PaddedTypeMap,
        ) -> BTreeSet<LambdaId<TypeInner<IndexOrPointer>>> {
            let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
                panic!()
            };
            let mut new_ids = BTreeSet::new();
            for id in ids.clone() {
                let id = id.map_type(|p| {
                    self.get_type_inner_for_hash(p, trace, map, true)
                });
                new_ids.insert(id);
            }
            new_ids
        }

        fn get_type_inner_for_hash(
            &mut self,
            p: TypePointer,
            trace: &FxHashSet<TypePointer>,
            map: &mut PaddedTypeMap,
            for_hash: bool,
        ) -> TypeInner<IndexOrPointer> {
            if for_hash {
                if let Some(t) = self.type_memo_for_hash.get(&p) {
                    return t.clone();
                }
            } else if let Some(t) = self.type_memo.get(&p) {
                return t.clone();
            }
            if trace.contains(&p) {
                return TypeInner::RecursionPoint(IndexOrPointer::Pointer(p));
            }
            let mut trace = trace.clone();
            trace.insert(p);
            let t = match &map.dereference_without_find(p) {
                Terminal::TypeMap(type_map) => {
                    let mut t = Vec::new();
                    for (type_id, normal_type) in &type_map.normals {
                        t.push((*type_id, normal_type.clone()));
                    }
                    TypeInner::Type(Type {
                        ts: t
                            .into_iter()
                            .map(|(id, args)| {
                                self.get_type_from_id_and_args_rec(
                                    id, &args, &trace, map, for_hash,
                                )
                            })
                            .collect(),
                        recursive: false,
                        reference: false,
                    })
                }
                Terminal::LambdaId(_) => panic!(),
            };
            let r = replace_pointer(t, p, 0);
            let mut t = r.t;
            if r.replaced {
                if let TypeInner::Type(t) = &mut t {
                    t.recursive = true;
                    t.reference = true;
                } else {
                    panic!()
                }
            };
            if !r.contains_pointer {
                let o = if for_hash {
                    self.type_memo_for_hash.insert(p, t.clone())
                } else {
                    self.type_memo.insert(p, t.clone())
                };
                debug_assert!(o.is_none());
            }
            t
        }

        fn get_type_from_id_and_args_rec(
            &mut self,
            id: TypeId,
            args: &[TypePointer],
            trace: &FxHashSet<TypePointer>,
            map: &mut PaddedTypeMap,
            for_hash: bool,
        ) -> TypeUnit<IndexOrPointer> {
            if let TypeId::Intrinsic(IntrinsicType::Fn) = id {
                debug_assert_eq!(args.len(), 3);
                let mut args = args.iter();
                let a = self.get_type_inner_for_hash(
                    *args.next().unwrap(),
                    trace,
                    map,
                    for_hash,
                );
                let b = self.get_type_inner_for_hash(
                    *args.next().unwrap(),
                    trace,
                    map,
                    for_hash,
                );
                let empty_trace;
                let lambda_id = self.get_lambda_ids(
                    *args.next().unwrap(),
                    if for_hash {
                        trace
                    } else {
                        empty_trace = Default::default();
                        &empty_trace
                    },
                    map,
                );
                TypeUnit::Fn(lambda_id, a, b)
            } else {
                TypeUnit::Normal {
                    id,
                    args: args
                        .iter()
                        .map(|t| {
                            self.get_type_inner_for_hash(
                                *t, trace, map, for_hash,
                            )
                        })
                        .collect(),
                }
            }
        }
    }

    pub struct ReplacePointerResult {
        t: TypeInner<IndexOrPointer>,
        replaced: bool,
        contains_pointer: bool,
    }

    fn replace_pointer(
        t: TypeInner<IndexOrPointer>,
        from: TypePointer,
        depth: u32,
    ) -> ReplacePointerResult {
        match t {
            TypeInner::RecursionPoint(IndexOrPointer::Index(i)) => {
                ReplacePointerResult {
                    t: TypeInner::RecursionPoint(IndexOrPointer::Index(i)),
                    replaced: false,
                    contains_pointer: i > depth,
                }
            }
            TypeInner::RecursionPoint(IndexOrPointer::Pointer(i)) => {
                if i == from {
                    ReplacePointerResult {
                        t: TypeInner::RecursionPoint(IndexOrPointer::Index(
                            depth,
                        )),
                        replaced: true,
                        contains_pointer: false,
                    }
                } else {
                    ReplacePointerResult {
                        t: TypeInner::RecursionPoint(IndexOrPointer::Pointer(
                            i,
                        )),
                        replaced: false,
                        contains_pointer: true,
                    }
                }
            }
            TypeInner::Type(t) => {
                let depth = t.recursive as u32 + depth;
                let mut new_t = Vec::new();
                let mut replaced = false;
                let mut contains_pointer = false;
                use TypeUnit::*;
                for u in t.ts {
                    match u {
                        Normal { id, args } => {
                            let args = args
                                .into_iter()
                                .map(|arg| {
                                    let r = replace_pointer(arg, from, depth);
                                    replaced |= r.replaced;
                                    contains_pointer |= r.contains_pointer;
                                    r.t
                                })
                                .collect();
                            new_t.push(Normal { id, args });
                        }
                        Fn(l, a, b) => {
                            let l = l
                                .into_iter()
                                .map(|l| {
                                    l.map_type(|t| {
                                        let r = replace_pointer(t, from, depth);
                                        replaced |= r.replaced;
                                        contains_pointer |= r.contains_pointer;
                                        r.t
                                    })
                                })
                                .collect();
                            let r = replace_pointer(a, from, depth);
                            replaced |= r.replaced;
                            contains_pointer |= r.contains_pointer;
                            let a = r.t;
                            let r = replace_pointer(b, from, depth);
                            replaced |= r.replaced;
                            contains_pointer |= r.contains_pointer;
                            let b = r.t;
                            new_t.push(Fn(l, a, b));
                        }
                    }
                }
                ReplacePointerResult {
                    t: TypeInner::Type(Type {
                        ts: new_t,
                        recursive: t.recursive,
                        reference: t.reference,
                    }),
                    replaced,
                    contains_pointer,
                }
            }
        }
    }
}

impl<R: Debug> Display for Type<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.reference {
            write!(f, "&")?;
        }
        if self.recursive {
            write!(f, "rec[")?;
        }
        match self.ts.len() {
            0 => write!(f, "∅"),
            1 => write!(f, "{}", self.ts.first().unwrap()),
            _ => write!(f, "{{{}}}", self.ts.iter().format(" | ")),
        }?;
        if self.recursive {
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl<R: Debug> Display for TypeInner<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInner::RecursionPoint(d) => {
                write!(f, "d{d:?}")
            }
            TypeInner::Type(t) => write!(f, "{t}"),
        }
    }
}

impl<R: Debug> Display for TypeUnit<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnit::*;
        match self {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicType::Fn));
                if args.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(f, "{}[{}]", id, args.iter().format(", "))
                }
            }
            Fn(id, a, b) => {
                let id_paren = id.len() >= 2;
                write!(
                    f,
                    "({a}) -{}{}{}-> {b}",
                    if id_paren { "(" } else { "" },
                    id.iter()
                        .format_with(" | ", |a, f| f(&format_args!("{}", a))),
                    if id_paren { ")" } else { "" },
                )
            }
        }
    }
}

impl Display for GlobalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

mod local_variable {
    use std::fmt::{Debug, Display};

    #[derive(Debug, PartialEq, Hash, Clone, Copy, Eq)]
    pub struct LocalVariable(usize);

    #[derive(Debug, PartialEq)]
    pub struct LocalVariableCollector<T>(Vec<T>);

    impl<T: Display> LocalVariableCollector<T> {
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

        pub fn map<U>(
            self,
            f: impl FnMut(T) -> U,
        ) -> LocalVariableCollector<U> {
            LocalVariableCollector(self.0.into_iter().map(f).collect())
        }
    }

    impl Display for LocalVariable {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }
}
