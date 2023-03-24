use crate::ast_step1::decl_id::DeclId;
use crate::ast_step2::{ConstructorId, TypeId};
use crate::ast_step3::{BasicFunction, DataDecl};
use crate::ast_step4::{TypeForHash, VariableId};
use crate::ast_step5::{self, get_tag_normal, FnArm, LambdaId, Pattern, Type};
use crate::intrinsics::IntrinsicType;
use fxhash::FxHashMap;
use smallvec::SmallVec;

#[derive(Debug)]
pub struct Ast {
    pub variable_decl: Vec<VariableDecl>,
    pub data_decl: Vec<DataDecl>,
    pub entry_point: LambdaId,
    pub functions: Vec<Function>,
    pub variable_names: FxHashMap<VariableId, String>,
    pub variable_types: FxHashMap<VariableId, Type>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub parameter: DeclId,
    pub body: Block,
    pub ret: VariableId,
    pub id: LambdaId,
    pub original_id: u32,
    pub origin_type: TypeForHash,
    pub context: Vec<DeclId>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub value: Block,
    pub ret: VariableId,
    pub decl_id: DeclId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

pub type Tag = SmallVec<[u32; 2]>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Constructor { id: ConstructorId, tag: Tag },
    I64 { value: String, tag: Tag },
    Str { value: String, tag: Tag },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(Option<DeclId>, Expr),
    Test(Tester, VariableId),
    TryCatch(Block, Block),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: LambdaId,
        context: Vec<DeclId>,
    },
    I64(String),
    Str(String),
    Ident(VariableId),
    Call {
        f: VariableId,
        a: VariableId,
        possible_functions: Vec<LambdaId>,
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
}

impl Ast {
    pub fn from(ast: ast_step5::Ast) -> Self {
        let mut env = Env {
            variable_types: FxHashMap::default(),
        };
        Self {
            variable_decl: ast
                .variable_decl
                .into_iter()
                .map(|d| env.variable_decl(d))
                .collect(),
            data_decl: ast.data_decl,
            entry_point: ast.entry_point,
            functions: ast
                .functions
                .into_iter()
                .map(|f| env.function(f))
                .collect(),
            variable_names: ast.variable_names,
            variable_types: env.variable_types,
        }
    }
}

struct Env {
    variable_types: FxHashMap<VariableId, Type>,
}

impl Env {
    fn function(&mut self, f: ast_step5::Function) -> Function {
        let mut instructions = Vec::new();
        self.variable_types
            .insert(VariableId::Local(f.parameter), f.parameter_type);
        let ret = self.collect(f.body.clone(), &mut instructions);
        if instructions.is_empty() {
            eprintln!("f.body = {:?}", f.body)
        }
        Function {
            parameter: f.parameter,
            body: Block { instructions },
            ret,
            id: f.id,
            original_id: f.original_id,
            origin_type: f.origin_type,
            context: f.context,
        }
    }

    fn variable_decl(&mut self, d: ast_step5::VariableDecl) -> VariableDecl {
        let mut instructions = Vec::new();
        let ret = self.collect(d.value, &mut instructions);
        VariableDecl {
            value: Block { instructions },
            ret,
            decl_id: d.decl_id,
        }
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: Type,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        let d = DeclId::new();
        self.variable_types.insert(VariableId::Local(d), t);
        instructions.push(Instruction::Assign(Some(d), e));
        VariableId::Local(d)
    }

    fn collect(
        &mut self,
        (e, t): ast_step5::ExprWithType,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        match e {
            ast_step5::Expr::Lambda { lambda_id, context } => self
                .expr_to_variable(
                    Expr::Lambda { lambda_id, context },
                    t,
                    instructions,
                ),
            ast_step5::Expr::Match {
                mut arms,
                arguments,
            } => {
                let ret_id = DeclId::new();
                if arms.len() == 1 {
                    self.collect_fn_arm(
                        arms.pop().unwrap(),
                        &arguments,
                        ret_id,
                        t,
                        instructions,
                    );
                } else {
                    let mut arms = arms
                        .into_iter()
                        .map(|a| {
                            let mut instructions = Vec::new();
                            self.collect_fn_arm(
                                a,
                                &arguments,
                                ret_id,
                                t.clone(),
                                &mut instructions,
                            );
                            Block { instructions }
                        })
                        .rev();
                    let a = arms.next().unwrap();
                    let b = arms.next().unwrap();
                    let e = arms.fold(Instruction::TryCatch(b, a), |acc, b| {
                        Instruction::TryCatch(
                            b,
                            Block {
                                instructions: vec![acc],
                            },
                        )
                    });
                    instructions.push(e);
                }
                VariableId::Local(ret_id)
            }
            ast_step5::Expr::Number(a) => {
                self.expr_to_variable(Expr::I64(a), t, instructions)
            }
            ast_step5::Expr::StrLiteral(a) => {
                self.expr_to_variable(Expr::Str(a), t, instructions)
            }
            ast_step5::Expr::Ident { variable_id } => variable_id,
            ast_step5::Expr::Call {
                possible_functions,
                f,
                a,
            } => {
                let f = self.collect(*f, instructions);
                let a = self.collect(*a, instructions);
                self.expr_to_variable(
                    Expr::Call {
                        f,
                        a,
                        possible_functions,
                    },
                    t,
                    instructions,
                )
            }
            ast_step5::Expr::DoBlock(mut es) => {
                let e = es.pop().unwrap();
                for e in es {
                    self.collect(e, instructions);
                }
                self.collect(e, instructions)
            }
            ast_step5::Expr::BasicCall { args, id } => {
                let args = args
                    .into_iter()
                    .map(|a| self.collect(a, instructions))
                    .collect();
                self.expr_to_variable(
                    Expr::BasicCall { args, id },
                    t,
                    instructions,
                )
            }
            ast_step5::Expr::Upcast { tag, value } => {
                let value = self.collect((*value, t.clone()), instructions);
                self.expr_to_variable(
                    Expr::Upcast { tag, value },
                    t,
                    instructions,
                )
            }
            ast_step5::Expr::Downcast { tag, value } => {
                let value = self.collect((*value, t.clone()), instructions);
                self.expr_to_variable(
                    Expr::Downcast { tag, value },
                    t,
                    instructions,
                )
            }
        }
    }

    fn collect_fn_arm(
        &mut self,
        arm: FnArm,
        arguments: &[DeclId],
        ret_id: DeclId,
        t: Type,
        instructions: &mut Vec<Instruction>,
    ) -> DeclId {
        self.variable_types.insert(VariableId::Local(ret_id), t);
        for (p, a) in arm.pattern.into_iter().zip(arguments) {
            self.pattern(p, VariableId::Local(*a), instructions);
        }
        let r = self.collect(arm.expr, instructions);
        instructions.push(Instruction::Assign(Some(ret_id), Expr::Ident(r)));
        ret_id
    }

    fn pattern(
        &mut self,
        p: Pattern,
        a: VariableId,
        instructions: &mut Vec<Instruction>,
    ) {
        if p.patterns.len() == 1 {
            let t = p.type_;
            let p = p.patterns.into_iter().next().unwrap();
            use ast_step5::PatternUnit::*;
            match p {
                I64(s) => {
                    let tag = get_tag_normal(
                        &t,
                        TypeId::Intrinsic(IntrinsicType::I64),
                    )
                    .unwrap();
                    instructions.push(Instruction::Test(
                        Tester::I64 { value: s, tag },
                        a,
                    ))
                }
                Str(s) => {
                    let tag = get_tag_normal(
                        &t,
                        TypeId::Intrinsic(IntrinsicType::String),
                    )
                    .unwrap();
                    instructions.push(Instruction::Test(
                        Tester::Str { value: s, tag },
                        a,
                    ))
                }
                Constructor { id } => {
                    let tag = get_tag_normal(&t, id.into()).unwrap();
                    instructions.push(Instruction::Test(
                        Tester::Constructor { id, tag },
                        a,
                    ))
                }
                Binder(b) => {
                    self.variable_types.insert(VariableId::Local(b), t);
                    instructions
                        .push(Instruction::Assign(Some(b), Expr::Ident(a)))
                }
                Underscore => (),
                TypeRestriction(_, _) => unimplemented!(),
                Apply {
                    pre_pattern,
                    function,
                    possible_functions,
                    post_pattern,
                } => {
                    self.pattern(pre_pattern, a, instructions);
                    let f = self.collect(function, instructions);
                    let e = Expr::Call {
                        f,
                        a,
                        possible_functions,
                    };
                    let d = self.expr_to_variable(e, t, instructions);
                    self.pattern(post_pattern, d, instructions);
                }
            }
        } else {
            unimplemented!()
        }
    }
}
