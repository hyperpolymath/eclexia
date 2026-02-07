// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! HIR to MIR lowering.
//!
//! Transforms the high-level HIR into control-flow graph based MIR.

use crate::*;
use eclexia_hir as hir;
use rustc_hash::FxHashMap;

/// Lowering context for HIR → MIR transformation
pub struct LoweringContext<'hir> {
    /// HIR file being lowered
    hir: &'hir hir::HirFile,
    /// MIR being built
    mir: MirFile,
    /// Current function being lowered
    current_function: Option<Function>,
    /// Map from HIR locals to MIR locals
    local_map: FxHashMap<hir::LocalId, LocalId>,
    /// Next local ID
    next_local: LocalId,
    /// Current basic block being built
    current_block: Option<BlockId>,
    /// Function name map (for resolving function calls)
    function_names: FxHashMap<SmolStr, SmolStr>,
}

impl<'hir> LoweringContext<'hir> {
    pub fn new(hir: &'hir hir::HirFile) -> Self {
        let mut function_names = FxHashMap::default();

        // Build function name map from HIR items
        for item in &hir.items {
            match item {
                hir::Item::Function(func) => {
                    function_names.insert(func.name.clone(), func.name.clone());
                }
                hir::Item::AdaptiveFunction(func) => {
                    function_names.insert(func.name.clone(), func.name.clone());
                }
                _ => {}
            }
        }

        Self {
            hir,
            mir: MirFile::new(),
            current_function: None,
            local_map: FxHashMap::default(),
            next_local: 0,
            current_block: None,
            function_names,
        }
    }

    /// Allocate a new local variable
    fn alloc_local(&mut self, name: SmolStr, ty: Ty, mutable: bool) -> LocalId {
        let id = self.next_local;
        self.next_local += 1;

        if let Some(func) = &mut self.current_function {
            func.locals.push(Local {
                id,
                name,
                ty,
                mutable,
            });
        }

        id
    }

    /// Get MIR local from HIR local
    fn get_local(&self, hir_local: hir::LocalId) -> Option<LocalId> {
        self.local_map.get(&hir_local).copied()
    }

    /// Allocate a new basic block
    fn alloc_block(&mut self, label: SmolStr) -> BlockId {
        if let Some(func) = &mut self.current_function {
            func.basic_blocks.alloc(BasicBlock {
                label,
                instructions: Vec::new(),
                terminator: Terminator::Unreachable,
            })
        } else {
            panic!("No current function")
        }
    }

    /// Emit an instruction to the current block
    fn emit(&mut self, span: Span, kind: InstructionKind) {
        if let Some(func) = &mut self.current_function {
            if let Some(block_id) = self.current_block {
                func.basic_blocks[block_id]
                    .instructions
                    .push(Instruction { span, kind });
            }
        }
    }

    /// Set the terminator for the current block
    fn terminate(&mut self, terminator: Terminator) {
        if let Some(func) = &mut self.current_function {
            if let Some(block_id) = self.current_block {
                func.basic_blocks[block_id].terminator = terminator;
            }
        }
    }

    /// Lower a HIR item
    fn lower_item(&mut self, item: &hir::Item) {
        match item {
            hir::Item::Function(func) => {
                let mir_func = self.lower_function(func);
                self.mir.functions.push(mir_func);
            }
            hir::Item::AdaptiveFunction(func) => {
                // For now, lower each solution as a separate function
                // In the future, this will create adaptive dispatch logic
                for solution in &func.solutions {
                    let mut solution_func = Function {
                        span: solution.span,
                        name: SmolStr::new(&format!("{}_{}", func.name, solution.name)),
                        params: Vec::new(),
                        return_ty: func.return_ty.clone(),
                        locals: Vec::new(),
                        basic_blocks: Arena::new(),
                        entry_block: BlockId::from_raw(la_arena::RawIdx::from_u32(0)),
                        resource_constraints: self.lower_constraints(&func.constraints),
                        is_adaptive: true,
                    };

                    // Lower solution body
                    self.current_function = Some(solution_func.clone());
                    self.local_map.clear();
                    self.next_local = 0;

                    // Create entry block
                    let entry = self.alloc_block(SmolStr::new("entry"));
                    solution_func.entry_block = entry;
                    self.current_block = Some(entry);
                    self.current_function = Some(solution_func);

                    // Lower body
                    self.lower_body(&solution.body);

                    // Extract and save function
                    if let Some(func) = self.current_function.take() {
                        self.mir.functions.push(func);
                    }
                }
            }
            hir::Item::TypeDef(_) | hir::Item::Const(_) => {
                // Type definitions and constants are already resolved
            }
        }
    }

    /// Lower a HIR function
    fn lower_function(&mut self, func: &hir::Function) -> Function {
        self.local_map.clear();
        self.next_local = 0;

        // Lower parameters
        let params: Vec<Local> = func
            .params
            .iter()
            .map(|p| {
                let id = self.next_local;
                self.next_local += 1;
                self.local_map.insert(p.local, id);
                Local {
                    id,
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                    mutable: false,
                }
            })
            .collect();

        let mut mir_func = Function {
            span: func.span,
            name: func.name.clone(),
            params,
            return_ty: func.return_ty.clone(),
            locals: Vec::new(),
            basic_blocks: Arena::new(),
            entry_block: BlockId::from_raw(la_arena::RawIdx::from_u32(0)),
            resource_constraints: self.lower_constraints(&func.constraints),
            is_adaptive: false,
        };

        // Set current function first
        self.current_function = Some(mir_func);

        // Create entry block
        let entry = self.alloc_block(SmolStr::new("entry"));
        if let Some(func) = &mut self.current_function {
            func.entry_block = entry;
        }
        self.current_block = Some(entry);

        // Lower function body
        self.lower_body(&func.body);

        // Extract function
        self.current_function.take().unwrap()
    }

    /// Lower resource constraints
    fn lower_constraints(&self, constraints: &[hir::ResourceConstraint]) -> Vec<ResourceConstraint> {
        constraints
            .iter()
            .map(|c| ResourceConstraint {
                resource: c.resource.clone(),
                dimension: c.dimension,
                op: match c.op {
                    hir::ConstraintOp::Lt => ConstraintOp::Lt,
                    hir::ConstraintOp::Le => ConstraintOp::Le,
                    hir::ConstraintOp::Gt => ConstraintOp::Gt,
                    hir::ConstraintOp::Ge => ConstraintOp::Ge,
                    hir::ConstraintOp::Eq => ConstraintOp::Eq,
                    hir::ConstraintOp::Ne => ConstraintOp::Ne,
                },
                bound: c.bound,
            })
            .collect()
    }

    /// Lower a function body
    fn lower_body(&mut self, body: &hir::Body) {
        // Lower statements
        for &stmt_id in &body.stmts {
            self.lower_stmt(stmt_id);
        }

        // Lower final expression or return unit
        if let Some(expr_id) = body.expr {
            let value = self.lower_expr(expr_id);
            self.terminate(Terminator::Return(Some(value)));
        } else {
            self.terminate(Terminator::Return(None));
        }
    }

    /// Lower a statement
    fn lower_stmt(&mut self, stmt_id: hir::StmtId) {
        let stmt = &self.hir.stmts[stmt_id];
        match &stmt.kind {
            hir::StmtKind::Let { local, init } => {
                // Get or create MIR local
                let mir_local = if let Some(&existing) = self.local_map.get(local) {
                    existing
                } else {
                    // Allocate new MIR local
                    let hir_local = &self.hir.locals[*local];
                    let id = self.next_local;
                    self.next_local += 1;
                    self.local_map.insert(*local, id);

                    // Add to current function's locals
                    if let Some(func) = &mut self.current_function {
                        func.locals.push(Local {
                            id,
                            name: hir_local.name.clone(),
                            ty: hir_local.ty.clone(),
                            mutable: hir_local.mutable,
                        });
                    }
                    id
                };

                if let Some(init_expr) = init {
                    let value = self.lower_expr(*init_expr);
                    self.emit(stmt.span, InstructionKind::Assign {
                        target: mir_local,
                        value,
                    });
                }
            }
            hir::StmtKind::Assign { place, value } => {
                let mir_value = self.lower_expr(*value);
                // Only handle local assignments for now
                if let hir::Place::Local(local) = place {
                    let mir_local = self.local_map[local];
                    self.emit(stmt.span, InstructionKind::Assign {
                        target: mir_local,
                        value: mir_value,
                    });
                }
            }
            hir::StmtKind::Expr(expr) => {
                self.lower_expr(*expr);
            }
            hir::StmtKind::Return(expr) => {
                let value = expr.map(|e| self.lower_expr(e));
                self.terminate(Terminator::Return(value));
            }
        }
    }

    /// Lower a place (lvalue)
    fn lower_place(&mut self, place: &hir::Place) -> Value {
        match place {
            hir::Place::Local(local) => Value::Local(self.local_map[local]),
            hir::Place::Field { .. } | hir::Place::Index { .. } => {
                // TODO: Implement field/index places
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }
        }
    }

    /// Lower an expression to a value
    fn lower_expr(&mut self, expr_id: hir::ExprId) -> Value {
        let expr = &self.hir.exprs[expr_id];
        match &expr.kind {
            hir::ExprKind::Literal(lit) => {
                let constant = match lit {
                    hir::Literal::Int(n) => Constant {
                        ty: Ty::Primitive(PrimitiveTy::Int),
                        kind: ConstantKind::Int(*n),
                    },
                    hir::Literal::Float(f) => Constant {
                        ty: Ty::Primitive(PrimitiveTy::Float),
                        kind: ConstantKind::Float(*f),
                    },
                    hir::Literal::Bool(b) => Constant {
                        ty: Ty::Primitive(PrimitiveTy::Bool),
                        kind: ConstantKind::Bool(*b),
                    },
                    hir::Literal::String(s) => Constant {
                        ty: Ty::Primitive(PrimitiveTy::String),
                        kind: ConstantKind::String(s.clone()),
                    },
                    hir::Literal::Unit => Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    },
                    _ => Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    },
                };
                Value::Constant(self.mir.constants.alloc(constant))
            }
            hir::ExprKind::Local(local) => Value::Local(self.local_map[local]),
            hir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs_val = self.lower_expr(*lhs);
                let rhs_val = self.lower_expr(*rhs);

                Value::Binary {
                    op: self.lower_binary_op(*op),
                    lhs: Box::new(lhs_val),
                    rhs: Box::new(rhs_val),
                }
            }
            hir::ExprKind::Unary { op, operand } => {
                let operand_val = self.lower_expr(*operand);

                Value::Unary {
                    op: self.lower_unary_op(*op),
                    operand: Box::new(operand_val),
                }
            }
            hir::ExprKind::Call { func, args } => {
                let arg_vals: Vec<Value> = args.iter().map(|&arg| self.lower_expr(arg)).collect();

                // Check if func is a function name reference
                let func_expr = &self.hir.exprs[*func];
                let func_val = if let hir::ExprKind::Local(local_id) = &func_expr.kind {
                    // Check if this local is actually a function reference
                    if !self.local_map.contains_key(local_id) {
                        // Not a real local variable - must be a function name
                        let local = &self.hir.locals[*local_id];
                        Value::Constant(self.mir.constants.alloc(Constant {
                            ty: func_expr.ty.clone(),
                            kind: ConstantKind::Function(local.name.clone()),
                        }))
                    } else {
                        let local = &self.hir.locals[*local_id];
                        if self.function_names.contains_key(&local.name) {
                            // This is a function reference - create function constant
                            Value::Constant(self.mir.constants.alloc(Constant {
                                ty: func_expr.ty.clone(),
                                kind: ConstantKind::Function(local.name.clone()),
                            }))
                        } else {
                            Value::Local(self.local_map[local_id])
                        }
                    }
                } else {
                    self.lower_expr(*func)
                };

                // Allocate a temporary for the result
                let result_local = self.next_local;
                self.next_local += 1;

                if let Some(f) = &mut self.current_function {
                    f.locals.push(Local {
                        id: result_local,
                        name: SmolStr::new(&format!("tmp{}", result_local)),
                        ty: expr.ty.clone(),
                        mutable: false,
                    });
                }

                // Emit call instruction
                self.emit(expr.span, InstructionKind::Call {
                    target: Some(result_local),
                    func: func_val,
                    args: arg_vals,
                    resource_budget: None,
                });

                Value::Local(result_local)
            }
            hir::ExprKind::If { condition, then_branch, else_branch } => {
                // Allocate a result temporary that both branches will assign to
                let result_local = self.next_local;
                self.next_local += 1;

                if let Some(f) = &mut self.current_function {
                    f.locals.push(Local {
                        id: result_local,
                        name: SmolStr::new(&format!("if_result{}", result_local)),
                        ty: expr.ty.clone(),
                        mutable: true,
                    });
                }

                let cond_val = self.lower_expr(*condition);

                // Create blocks for then, else, and merge
                let then_block = self.alloc_block(SmolStr::new("then"));
                let else_block = self.alloc_block(SmolStr::new("else"));
                let merge_block = self.alloc_block(SmolStr::new("merge"));

                // Branch on condition
                self.terminate(Terminator::Branch {
                    condition: cond_val,
                    then_block,
                    else_block,
                });

                // Lower then branch
                self.current_block = Some(then_block);
                if let Some(ref body_expr) = then_branch.expr {
                    let then_val = self.lower_expr(*body_expr);
                    self.emit(expr.span, InstructionKind::Assign {
                        target: result_local,
                        value: then_val,
                    });
                }
                self.terminate(Terminator::Goto(merge_block));

                // Lower else branch
                self.current_block = Some(else_block);
                if let Some(ref else_b) = else_branch {
                    if let Some(ref body_expr) = else_b.expr {
                        let else_val = self.lower_expr(*body_expr);
                        self.emit(expr.span, InstructionKind::Assign {
                            target: result_local,
                            value: else_val,
                        });
                    }
                } else {
                    // No else branch - assign unit
                    let unit_val = Value::Constant(self.mir.constants.alloc(Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    }));
                    self.emit(expr.span, InstructionKind::Assign {
                        target: result_local,
                        value: unit_val,
                    });
                }
                self.terminate(Terminator::Goto(merge_block));

                // Merge block - result is in the temporary
                self.current_block = Some(merge_block);
                Value::Local(result_local)
            }
            _ => {
                // TODO: Implement other expression kinds
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }
        }
    }

    fn lower_binary_op(&self, op: hir::BinaryOp) -> BinaryOp {
        match op {
            hir::BinaryOp::Add => BinaryOp::Add,
            hir::BinaryOp::Sub => BinaryOp::Sub,
            hir::BinaryOp::Mul => BinaryOp::Mul,
            hir::BinaryOp::Div => BinaryOp::Div,
            hir::BinaryOp::Rem => BinaryOp::Rem,
            hir::BinaryOp::Pow => BinaryOp::Mul, // TODO: Implement Pow properly
            hir::BinaryOp::Eq => BinaryOp::Eq,
            hir::BinaryOp::Ne => BinaryOp::Ne,
            hir::BinaryOp::Lt => BinaryOp::Lt,
            hir::BinaryOp::Le => BinaryOp::Le,
            hir::BinaryOp::Gt => BinaryOp::Gt,
            hir::BinaryOp::Ge => BinaryOp::Ge,
            hir::BinaryOp::And => BinaryOp::And,
            hir::BinaryOp::Or => BinaryOp::Or,
            hir::BinaryOp::BitAnd => BinaryOp::BitAnd,
            hir::BinaryOp::BitOr => BinaryOp::BitOr,
            hir::BinaryOp::BitXor => BinaryOp::BitXor,
            hir::BinaryOp::Shl => BinaryOp::Shl,
            hir::BinaryOp::Shr => BinaryOp::Shr,
            hir::BinaryOp::Range => BinaryOp::Range,
            hir::BinaryOp::RangeInclusive => BinaryOp::RangeInclusive,
        }
    }

    fn lower_unary_op(&self, op: hir::UnaryOp) -> UnaryOp {
        match op {
            hir::UnaryOp::Neg => UnaryOp::Neg,
            hir::UnaryOp::Not => UnaryOp::Not,
            hir::UnaryOp::BitNot => UnaryOp::BitNot,
        }
    }
}

/// Lower a HIR file to MIR
pub fn lower_hir_file(hir: &hir::HirFile) -> MirFile {
    let mut ctx = LoweringContext::new(hir);

    for item in &hir.items {
        ctx.lower_item(item);
    }

    ctx.mir
}
