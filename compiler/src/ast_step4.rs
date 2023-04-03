mod padded_type_map;

pub use self::padded_type_map::{
    PaddedTypeMap, ReplaceMap, Terminal, TypePointer,
};
use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::{ApplyPattern, ConstructorId, PatternUnit, TypeId};
use crate::ast_step3::{self, BasicFunction, DataDecl, FnArm};
use crate::ast_step5::Type;
use crate::intrinsics::IntrinsicType;
use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
use std::fmt::Display;

#[derive(Debug)]
pub struct Ast {
    pub variable_decls: Vec<VariableDecl>,
    pub data_decls: Vec<DataDecl>,
    pub entry_point: DeclId,
    pub type_of_entry_point: TypePointer,
    pub local_variable_types_old: FxHashMap<LocalVariable, TypePointer>,
    pub type_map: PaddedTypeMap,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LocalVariable(DeclId);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum VariableId {
    Local(LocalVariable),
    Global(DeclId, ReplaceMap, TypePointer),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct LambdaId<T> {
    pub id: u32,
    pub root_t: T,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub value: Block,
    pub ret: VariableId,
    pub decl_id: DeclId,
    pub name: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Constructor { id: ConstructorId },
    I64 { value: String },
    Str { value: String },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(Option<LocalVariable>, Expr, TypePointer),
    Test(Tester, VariableId),
    TryCatch(Block, Block),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: LambdaId<TypePointer>,
        context: Vec<LocalVariable>,
        parameter: LocalVariable,
        body: Block,
        ret: VariableId,
    },
    I64(String),
    Str(String),
    Ident(VariableId),
    Call {
        f: VariableId,
        a: VariableId,
    },
    BasicCall {
        args: Vec<VariableId>,
        id: BasicFunction,
    },
}

impl Ast {
    pub fn from(ast: ast_step3::Ast) -> Self {
        let mut env = Env {
            type_map: PaddedTypeMap::default(),
            global_variable_types: Default::default(),
            local_variable_types: Default::default(),
            global_variables_step3: ast
                .variable_decls
                .into_iter()
                .map(|d| (d.decl_id, d))
                .collect(),
            global_variables_done: Default::default(),
            data_decls: ast.data_decl.iter().map(|d| (d.decl_id, d)).collect(),
            used_local_variables: FxHashSet::default(),
            defined_local_variables: FxHashSet::default(),
            trace: Default::default(),
            lambda_count: 0,
        };
        let entry_point = ast
            .entry_point
            .unwrap_or_else(|| panic!("entry point not found"));
        let (type_of_entry_point, rec) = env.get_type_global(entry_point);
        let (p, _, _) = env.type_map.get_fn(type_of_entry_point);
        env.type_map.insert_normal(
            p,
            TypeId::Intrinsic(IntrinsicType::Unit),
            Vec::new(),
        );
        debug_assert!(!rec);
        let variable_decls = env.global_variables_done;
        let local_variable_types = env.local_variable_types;
        let type_map = env.type_map;
        Self {
            variable_decls,
            data_decls: ast.data_decl,
            entry_point,
            type_of_entry_point,
            local_variable_types_old: local_variable_types,
            type_map,
        }
    }
}

struct Env<'a> {
    type_map: PaddedTypeMap,
    global_variable_types: FxHashMap<DeclId, TypePointer>,
    local_variable_types: FxHashMap<LocalVariable, TypePointer>,
    global_variables_step3: FxHashMap<DeclId, ast_step3::VariableDecl<'a>>,
    global_variables_done: Vec<VariableDecl>,
    data_decls: FxHashMap<DeclId, &'a ast_step3::DataDecl>,
    used_local_variables: FxHashSet<LocalVariable>,
    defined_local_variables: FxHashSet<LocalVariable>,
    trace: FxHashMap<DeclId, TypePointer>,
    lambda_count: u32,
}

impl<'a> Env<'a> {
    fn get_type_global(&mut self, decl_id: DeclId) -> (TypePointer, bool) {
        if let Some(p) = self.trace.get(&decl_id) {
            (*p, true)
        } else if let Some(p) = self.global_variable_types.get(&decl_id) {
            (*p, false)
        } else {
            let d = self.global_variables_step3.remove(&decl_id).unwrap();
            let p = self.type_map.new_pointer();
            self.trace.insert(decl_id, p);
            let free_variable_len = self
                .used_local_variables
                .len()
                .saturating_sub(self.defined_local_variables.len());
            let mut instructions = Vec::new();
            let ret = self.expr(d.value, p, p, &mut instructions);
            self.trace.remove(&decl_id);
            let d = VariableDecl {
                value: Block { instructions },
                decl_id,
                ret,
                name: d.name.to_string(),
            };
            debug_assert!(
                free_variable_len
                    >= self
                        .used_local_variables
                        .len()
                        .saturating_sub(self.defined_local_variables.len())
            );
            self.global_variable_types.insert(decl_id, p);
            self.global_variables_done.push(d);
            (p, false)
        }
    }

    fn expr(
        &mut self,
        e: ast_step3::Expr,
        type_pointer: TypePointer,
        root_t: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        match e {
            ast_step3::Expr::Lambda(arms) => {
                let param_len = arms[0].pattern.len();
                let args = (0..param_len)
                    .map(|_| {
                        let t = self.type_map.new_pointer();
                        self.new_local_variable(t)
                    })
                    .collect_vec();
                let used_local_variables_tmp =
                    std::mem::take(&mut self.used_local_variables);
                let defined_local_variables_tmp =
                    std::mem::take(&mut self.defined_local_variables);
                let mut body_instructions = Vec::new();
                let ret_type = self.type_map.new_pointer();
                let mut ret = if arms.len() == 1 {
                    let arm = arms.into_iter().next().unwrap();
                    self.fn_arm(
                        arm,
                        ret_type,
                        root_t,
                        &args,
                        &mut body_instructions,
                    )
                } else {
                    let ret = self.new_local_variable(ret_type);
                    let mut b = arms
                        .into_iter()
                        .map(|arm| {
                            let mut is = Vec::new();
                            let d = self
                                .fn_arm(arm, ret_type, root_t, &args, &mut is);
                            is.push(Instruction::Assign(
                                Some(ret),
                                Expr::Ident(d),
                                ret_type,
                            ));
                            Block { instructions: is }
                        })
                        .reduce(|a, b| Block {
                            instructions: vec![Instruction::TryCatch(a, b)],
                        })
                        .unwrap();
                    body_instructions.append(&mut b.instructions);
                    VariableId::Local(ret)
                };
                let mut context: Vec<_> = self
                    .used_local_variables
                    .iter()
                    .filter(|d| !self.defined_local_variables.contains(d))
                    .copied()
                    .chain(args)
                    .collect();
                for _ in 0..param_len {
                    let lambda_id = LambdaId {
                        id: self.lambda_count,
                        root_t,
                    };
                    self.lambda_count += 1;
                    let parameter = context.pop().unwrap();
                    let fn_id = self.type_map.new_lambda_id_pointer();
                    self.type_map.insert_lambda_id(fn_id, lambda_id.clone());
                    let t = self.type_map.new_pointer();
                    self.type_map.insert_function(
                        t,
                        self.local_variable_types[&parameter],
                        self.variable_id_to_type(&ret),
                        fn_id,
                    );
                    let e = Expr::Lambda {
                        lambda_id,
                        context: context.clone(),
                        parameter,
                        body: Block {
                            instructions: body_instructions,
                        },
                        ret,
                    };
                    body_instructions = Vec::new();
                    ret = self
                        .expr_to_variable(e, t, &mut body_instructions)
                        .into();
                }
                self.type_map
                    .union(ret.type_(&self.local_variable_types), type_pointer);
                instructions.append(&mut body_instructions);
                self.used_local_variables
                    .extend(used_local_variables_tmp.into_iter());
                self.defined_local_variables
                    .extend(defined_local_variables_tmp.into_iter());
                ret
            }
            ast_step3::Expr::Number(s) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(crate::intrinsics::IntrinsicType::I64),
                    Vec::new(),
                );
                self.expr_to_variable(
                    Expr::I64(s.to_string()),
                    type_pointer,
                    instructions,
                )
                .into()
            }
            ast_step3::Expr::StrLiteral(s) => {
                self.type_map.insert_normal(
                    type_pointer,
                    TypeId::Intrinsic(crate::intrinsics::IntrinsicType::String),
                    Vec::new(),
                );
                self.expr_to_variable(
                    Expr::Str(s.to_string()),
                    type_pointer,
                    instructions,
                )
                .into()
            }
            ast_step3::Expr::Ident {
                name: _,
                variable_id: ast_step3::VariableId::Local(d),
            } => {
                let d = LocalVariable(d);
                self.used_local_variables.insert(d);
                let t = self.local_variable_types[&d];
                self.type_map.union(type_pointer, t);
                self.expr_to_variable(
                    Expr::Ident(VariableId::Local(d)),
                    t,
                    instructions,
                )
                .into()
            }
            ast_step3::Expr::Ident {
                name: _,
                variable_id: ast_step3::VariableId::Global(d),
            } => {
                let (p, is_recursive) = self.get_type_global(d);
                if is_recursive {
                    self.type_map.union(p, type_pointer);
                    VariableId::Global(d, Default::default(), p)
                } else {
                    let mut replace_map = Default::default();
                    let v_cloned =
                        self.type_map.clone_pointer(p, &mut replace_map);
                    self.type_map.union(type_pointer, v_cloned);
                    VariableId::Global(d, replace_map, type_pointer)
                }
            }
            ast_step3::Expr::Ident {
                name: _,
                variable_id:
                    ast_step3::VariableId::IntrinsicVariable(_)
                    | ast_step3::VariableId::IntrinsicConstructor(_)
                    | ast_step3::VariableId::Constructor(_)
                    | ast_step3::VariableId::FieldAccessor { .. },
            } => {
                panic!()
            }
            ast_step3::Expr::Call(f, a) => {
                let f_t = self.type_map.new_pointer();
                let a_t = self.type_map.new_pointer();
                let f = self.expr(*f, f_t, root_t, instructions);
                let a = self.expr(*a, a_t, root_t, instructions);
                self.call(f, f_t, a, a_t, type_pointer, instructions).into()
            }
            ast_step3::Expr::DoBlock(mut es) => {
                let e = es.pop().unwrap();
                for e in es {
                    let t = self.type_map.new_pointer();
                    self.expr(e, t, root_t, instructions);
                }
                self.expr(e, type_pointer, root_t, instructions)
            }
            ast_step3::Expr::IntrinsicCall { args, id } => {
                let (args, arg_ps): (Vec<_>, Vec<_>) = args
                    .into_iter()
                    .map(|a| {
                        let p = self.type_map.new_pointer();
                        (self.expr(a, p, root_t, instructions), p)
                    })
                    .unzip();
                match id {
                    BasicFunction::Intrinsic(i) => {
                        let ret_type = i.runtime_return_type();
                        unify_type_pointer_with_type(
                            &ret_type,
                            type_pointer,
                            &mut self.type_map,
                        );
                    }
                    BasicFunction::Construction(i) => {
                        self.type_map.insert_normal(
                            type_pointer,
                            i.into(),
                            arg_ps,
                        );
                    }
                    BasicFunction::FieldAccessor { constructor, field } => {
                        debug_assert_eq!(args.len(), 1);
                        let args_p = (0..self.data_decls[&constructor]
                            .field_len)
                            .map(|_| self.type_map.new_pointer())
                            .collect_vec();
                        self.type_map.union(type_pointer, args_p[field]);
                        self.type_map.insert_normal(
                            arg_ps[0],
                            TypeId::DeclId(constructor),
                            args_p,
                        );
                    }
                }
                self.expr_to_variable(
                    Expr::BasicCall { args, id },
                    type_pointer,
                    instructions,
                )
                .into()
            }
        }
    }

    fn variable_id_to_type(&self, v: &VariableId) -> TypePointer {
        match v {
            VariableId::Local(d) => self.local_variable_types[d],
            VariableId::Global(_, _, t) => *t,
        }
    }

    fn call(
        &mut self,
        f: VariableId,
        f_t: TypePointer,
        a: VariableId,
        a_t: TypePointer,
        ret_t: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) -> LocalVariable {
        let (arg, ret, _) = self.type_map.get_fn(f_t);
        self.type_map.union(a_t, arg);
        self.type_map.union(ret, ret_t);
        self.expr_to_variable(Expr::Call { f, a }, ret_t, instructions)
    }

    fn fn_arm(
        &mut self,
        arm: FnArm,
        ret_type: TypePointer,
        root_t: TypePointer,
        args: &[LocalVariable],
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        for (p, operand) in arm.pattern.into_iter().zip_eq(args) {
            self.pattern(p, *operand, root_t, instructions)
        }
        self.expr(arm.expr, ret_type, root_t, instructions)
    }

    fn pattern(
        &mut self,
        p: ast_step3::Pattern,
        operand: LocalVariable,
        root_t: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) {
        let mut p = p.0.into_iter();
        let mut block = Vec::new();
        self.pattern_unit(p.next().unwrap(), operand, root_t, &mut block);
        for p in p {
            let mut b = Vec::new();
            self.pattern_unit(p, operand, root_t, &mut b);
            block = vec![Instruction::TryCatch(
                Block {
                    instructions: block,
                },
                Block { instructions: b },
            )];
        }
        instructions.append(&mut block);
    }

    fn pattern_unit(
        &mut self,
        p: PatternUnit<(), ast_step3::Expr>,
        operand: LocalVariable,
        root_t: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) {
        let t = self.local_variable_types[&operand];
        match p {
            PatternUnit::I64(s) => {
                instructions.push(Instruction::Test(
                    Tester::I64 {
                        value: s.to_string(),
                    },
                    operand.into(),
                ));
            }
            PatternUnit::Str(s) => {
                instructions.push(Instruction::Test(
                    Tester::Str {
                        value: s.to_string(),
                    },
                    operand.into(),
                ));
            }
            PatternUnit::Constructor { id, args } => {
                instructions.push(Instruction::Test(
                    Tester::Constructor { id },
                    operand.into(),
                ));
                if !args.is_empty() {
                    let constructor = if let ConstructorId::DeclId(id) = id {
                        id
                    } else {
                        panic!()
                    };
                    let arg_ts = args
                        .iter()
                        .map(|_| self.type_map.new_pointer())
                        .collect_vec();
                    self.type_map.insert_normal(t, id.into(), arg_ts.clone());
                    for (field, ((a, _), t)) in
                        args.into_iter().zip_eq(arg_ts).enumerate()
                    {
                        let d = self.expr_to_variable(
                            Expr::BasicCall {
                                args: vec![operand.into()],
                                id: BasicFunction::FieldAccessor {
                                    constructor,
                                    field,
                                },
                            },
                            t,
                            instructions,
                        );
                        self.pattern(a, d, root_t, instructions);
                    }
                }
            }
            PatternUnit::Binder(_, d, _)
            | PatternUnit::ResolvedBinder(d, _) => {
                let d = LocalVariable(d);
                debug_assert!(!self.local_variable_types.contains_key(&d));
                self.defined_local_variables.insert(d);
                self.local_variable_types.insert(d, t);
                instructions.push(Instruction::Assign(
                    Some(d),
                    Expr::Ident(operand.into()),
                    t,
                ));
            }
            PatternUnit::Underscore => (),
            PatternUnit::TypeRestriction(_, _) => {
                unimplemented!()
            }
            PatternUnit::Apply(pre_pattern, applications) => {
                self.pattern(*pre_pattern, operand, root_t, instructions);
                for ApplyPattern {
                    function,
                    post_pattern,
                } in applications
                {
                    let fp = self.type_map.new_pointer();
                    let (ap, rp, _) = self.type_map.get_fn(fp);
                    self.type_map
                        .union(ap, self.local_variable_types[&operand]);
                    let f = self.expr(function, fp, root_t, instructions);
                    let operand = self.expr_to_variable(
                        Expr::Call {
                            f,
                            a: operand.into(),
                        },
                        rp,
                        instructions,
                    );
                    self.pattern(post_pattern, operand, root_t, instructions);
                }
            }
        }
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) -> LocalVariable {
        let d = self.new_local_variable(t);
        instructions.push(Instruction::Assign(Some(d), e, t));
        d
    }

    fn new_local_variable(&mut self, t: TypePointer) -> LocalVariable {
        let l = LocalVariable(DeclId::new());
        self.local_variable_types.insert(l, t);
        l
    }
}

impl<T: Display> Display for LambdaId<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}({})", self.id, self.root_t)
    }
}

impl From<LocalVariable> for VariableId {
    fn from(value: LocalVariable) -> Self {
        VariableId::Local(value)
    }
}

fn unify_type_pointer_with_type(
    t: &Type,
    p: TypePointer,
    map: &mut PaddedTypeMap,
) {
    for t in t.iter() {
        use crate::ast_step5::TypeUnit::*;
        if let Normal { id, args } = t {
            let mut p_args = Vec::with_capacity(args.len());
            for a in args {
                if let crate::ast_step5::TypeInner::Type(a) = a {
                    let p = map.new_pointer();
                    unify_type_pointer_with_type(a, p, map);
                    p_args.push(p);
                } else {
                    unimplemented!()
                }
            }
            map.insert_normal(p, *id, p_args);
        } else {
            unimplemented!()
        }
    }
}

impl VariableId {
    pub fn type_(
        &self,
        local_variable_types: &FxHashMap<LocalVariable, TypePointer>,
    ) -> TypePointer {
        match self {
            VariableId::Local(l) => local_variable_types[l],
            VariableId::Global(_, _, p) => *p,
        }
    }
}

impl Display for LocalVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
