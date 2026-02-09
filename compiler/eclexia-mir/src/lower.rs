// SPDX-License-Identifier: PMPL-1.0-or-later
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
    /// Loop stack for break/continue resolution: (label, header_block, exit_block)
    loop_stack: Vec<(Option<SmolStr>, BlockId, BlockId)>,
    /// Counter for generating unique lambda function names
    lambda_counter: u32,
}

impl<'hir> LoweringContext<'hir> {
    /// Create a new MIR lowering context from a HIR file
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
            loop_stack: Vec::new(),
            lambda_counter: 0,
        }
    }

    /// Allocate a new local variable
    #[allow(dead_code)]
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
    #[allow(dead_code)]
    fn get_local(&self, hir_local: hir::LocalId) -> Option<LocalId> {
        self.local_map.get(&hir_local).copied()
    }

    /// Allocate a new basic block
    fn alloc_block(&mut self, label: SmolStr) -> BlockId {
        let func = self.current_function.as_mut()
            .expect("BUG: alloc_block called without current function — this is an internal compiler error");
        func.basic_blocks.alloc(BasicBlock {
            label,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        })
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
                    self.local_map.clear();
                    self.next_local = 0;

                    // Register parent adaptive function parameters so solution bodies
                    // can reference them (solutions share the parent's parameter scope).
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

                    let solution_func = Function {
                        span: solution.span,
                        name: SmolStr::new(format!("{}_{}", func.name, solution.name)),
                        params,
                        return_ty: func.return_ty.clone(),
                        locals: Vec::new(),
                        basic_blocks: Arena::new(),
                        entry_block: BlockId::from_raw(la_arena::RawIdx::from_u32(0)),
                        resource_constraints: self.lower_constraints(&func.constraints),
                        is_adaptive: true,
                    };

                    // Set current function first, then allocate entry block in-place
                    // (must not clone-then-replace, or the arena allocation is lost).
                    self.current_function = Some(solution_func);
                    let entry = self.alloc_block(SmolStr::new("entry"));
                    if let Some(f) = &mut self.current_function {
                        f.entry_block = entry;
                    }
                    self.current_block = Some(entry);

                    // Lower body
                    self.lower_body(&solution.body);

                    // Extract and save function
                    if let Some(func) = self.current_function.take() {
                        self.mir.functions.push(func);
                    }
                }
            }
            hir::Item::TypeDef(_) | hir::Item::Const(_)
            | hir::Item::TraitDecl { .. } | hir::Item::ImplBlock { .. }
            | hir::Item::Module { .. } | hir::Item::Static { .. }
            | hir::Item::Error(_) => {
                // Type definitions, constants, declarations, and error items don't produce MIR functions
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

        let mir_func = Function {
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
        self.current_function.take()
            .expect("BUG: current_function is None after lowering — this is an internal compiler error")
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
                match place {
                    hir::Place::Local(local) => {
                        let mir_local = self.local_map[local];
                        self.emit(stmt.span, InstructionKind::Assign {
                            target: mir_local,
                            value: mir_value,
                        });
                    }
                    hir::Place::Field { .. } | hir::Place::Index { .. } => {
                        // Lower the place to a pointer value, then store
                        let ptr_val = self.lower_place(place);
                        self.emit(stmt.span, InstructionKind::Store {
                            ptr: ptr_val,
                            value: mir_value,
                        });
                    }
                }
            }
            hir::StmtKind::Expr(expr) => {
                self.lower_expr(*expr);
            }
            hir::StmtKind::Return(expr) => {
                let value = expr.map(|e| self.lower_expr(e));
                self.terminate(Terminator::Return(value));
            }
            hir::StmtKind::InfiniteLoop { label, body } => {
                // Create loop header and body blocks
                let loop_header = self.alloc_block(SmolStr::new("loop_header"));
                let loop_body = self.alloc_block(SmolStr::new("loop_body"));
                let loop_exit = self.alloc_block(SmolStr::new("loop_exit"));

                // Push loop onto stack for break/continue resolution
                self.loop_stack.push((label.clone(), loop_header, loop_exit));

                self.terminate(Terminator::Goto(loop_header));

                // Set up header to branch to body
                self.current_block = Some(loop_header);
                self.terminate(Terminator::Goto(loop_body));

                self.current_block = Some(loop_body);
                self.lower_body(body);
                self.terminate(Terminator::Goto(loop_header));

                // Pop loop from stack
                self.loop_stack.pop();

                self.current_block = Some(loop_exit);
            }
            hir::StmtKind::Break { label, value } => {
                // Evaluate break value if present (for side effects)
                if let Some(val_expr) = value {
                    self.lower_expr(*val_expr);
                }
                // Find the matching loop exit block on the stack
                let exit_block = self.find_loop_exit(label.as_ref());
                if let Some(exit) = exit_block {
                    self.terminate(Terminator::Goto(exit));
                    // Create a new unreachable block for any code after break
                    let dead_block = self.alloc_block(SmolStr::new("post_break"));
                    self.current_block = Some(dead_block);
                }
            }
            hir::StmtKind::Continue { label } => {
                // Find the matching loop header block on the stack
                let header_block = self.find_loop_header(label.as_ref());
                if let Some(header) = header_block {
                    self.terminate(Terminator::Goto(header));
                    // Create a new unreachable block for any code after continue
                    let dead_block = self.alloc_block(SmolStr::new("post_continue"));
                    self.current_block = Some(dead_block);
                }
            }
            hir::StmtKind::Error => {
                // Error statements are silently skipped during lowering
            }
        }
    }

    /// Lower a place (lvalue) to a value suitable for Store instructions
    fn lower_place(&mut self, place: &hir::Place) -> Value {
        match place {
            hir::Place::Local(local) => Value::Local(self.local_map[local]),
            hir::Place::Field { base, field } => {
                let base_val = self.lower_place(base);
                Value::Field {
                    base: Box::new(base_val),
                    field: field.clone(),
                }
            }
            hir::Place::Index { base, index } => {
                let base_val = self.lower_place(base);
                let index_val = self.lower_expr(*index);
                Value::Index {
                    base: Box::new(base_val),
                    index: Box::new(index_val),
                }
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
            hir::ExprKind::Local(local) => {
                if let Some(&mir_local) = self.local_map.get(local) {
                    Value::Local(mir_local)
                } else {
                    // Unknown local — produce a unit constant rather than panicking.
                    // This can happen when lowering incomplete ASTs (e.g. error recovery).
                    let constant = Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    };
                    Value::Constant(self.mir.constants.alloc(constant))
                }
            }
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
                        name: SmolStr::new(format!("tmp{}", result_local)),
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
                        name: SmolStr::new(format!("if_result{}", result_local)),
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
            hir::ExprKind::Loop { condition, body } => {
                // While loop: condition + body
                let loop_header = self.alloc_block(SmolStr::new("while_header"));
                let loop_body = self.alloc_block(SmolStr::new("while_body"));
                let loop_exit = self.alloc_block(SmolStr::new("while_exit"));

                // Push loop onto stack (while loops have no label)
                self.loop_stack.push((None, loop_header, loop_exit));

                self.terminate(Terminator::Goto(loop_header));

                self.current_block = Some(loop_header);
                let cond_val = self.lower_expr(*condition);
                self.terminate(Terminator::Branch {
                    condition: cond_val,
                    then_block: loop_body,
                    else_block: loop_exit,
                });

                self.current_block = Some(loop_body);
                self.lower_body(body);
                self.terminate(Terminator::Goto(loop_header));

                // Pop loop from stack
                self.loop_stack.pop();

                self.current_block = Some(loop_exit);
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::Block(body) => {
                // Lower block: evaluate statements, return final expression
                for &stmt_id in &body.stmts {
                    self.lower_stmt(stmt_id);
                }
                if let Some(expr_id) = body.expr {
                    self.lower_expr(expr_id)
                } else {
                    Value::Constant(self.mir.constants.alloc(Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    }))
                }
            }

            hir::ExprKind::Tuple(elems) | hir::ExprKind::Array(elems) => {
                // Allocate a result temporary for the aggregate
                let result_local = self.next_local;
                self.next_local += 1;

                if let Some(f) = &mut self.current_function {
                    f.locals.push(Local {
                        id: result_local,
                        name: SmolStr::new(format!("aggregate{}", result_local)),
                        ty: expr.ty.clone(),
                        mutable: false,
                    });
                }

                // Evaluate each element and assign to indexed positions
                for (i, &elem) in elems.iter().enumerate() {
                    let elem_val = self.lower_expr(elem);
                    // Store each element value to the aggregate via indexed Store
                    let idx_const = self.mir.constants.alloc(Constant {
                        ty: Ty::Primitive(PrimitiveTy::Int),
                        kind: ConstantKind::Int(i as i64),
                    });
                    self.emit(expr.span, InstructionKind::Store {
                        ptr: Value::Index {
                            base: Box::new(Value::Local(result_local)),
                            index: Box::new(Value::Constant(idx_const)),
                        },
                        value: elem_val,
                    });
                }

                Value::Local(result_local)
            }

            hir::ExprKind::Field { expr: base, field } => {
                let base_val = self.lower_expr(*base);
                Value::Field {
                    base: Box::new(base_val),
                    field: field.clone(),
                }
            }

            hir::ExprKind::Index { expr: base, index } => {
                let base_val = self.lower_expr(*base);
                let index_val = self.lower_expr(*index);
                Value::Index {
                    base: Box::new(base_val),
                    index: Box::new(index_val),
                }
            }

            hir::ExprKind::Cast { expr: inner, target_ty } => {
                let inner_val = self.lower_expr(*inner);
                Value::Cast {
                    value: Box::new(inner_val),
                    target_ty: target_ty.clone(),
                }
            }

            hir::ExprKind::Try(inner) => {
                // Try operator: evaluate inner, branch on ok/err
                let inner_val = self.lower_expr(*inner);

                // Allocate a temporary for the result
                let result_local = self.next_local;
                self.next_local += 1;
                if let Some(f) = &mut self.current_function {
                    f.locals.push(Local {
                        id: result_local,
                        name: SmolStr::new(format!("try_result{}", result_local)),
                        ty: expr.ty.clone(),
                        mutable: true,
                    });
                }

                // Assign inner value to temporary (the ok path unwraps)
                self.emit(expr.span, InstructionKind::Assign {
                    target: result_local,
                    value: inner_val.clone(),
                });

                // Create ok/err/merge blocks
                let ok_block = self.alloc_block(SmolStr::new("try_ok"));
                let err_block = self.alloc_block(SmolStr::new("try_err"));
                let merge_block = self.alloc_block(SmolStr::new("try_merge"));

                // Branch: for now use the inner value as the condition
                // (non-error values are truthy, error values are falsy)
                self.terminate(Terminator::Branch {
                    condition: inner_val,
                    then_block: ok_block,
                    else_block: err_block,
                });

                // Ok path: result is already assigned, continue
                self.current_block = Some(ok_block);
                self.terminate(Terminator::Goto(merge_block));

                // Err path: propagate error by returning early
                self.current_block = Some(err_block);
                self.terminate(Terminator::Return(Some(Value::Local(result_local))));

                // Merge block: continue with unwrapped value
                self.current_block = Some(merge_block);
                Value::Local(result_local)
            }

            hir::ExprKind::Borrow { expr: inner, .. } => {
                // Borrow: evaluate inner (no actual borrow tracking in MIR yet)
                self.lower_expr(*inner)
            }

            hir::ExprKind::Deref(inner) => {
                // Deref: evaluate inner (no actual deref in MIR yet)
                let inner_val = self.lower_expr(*inner);
                Value::Load { ptr: Box::new(inner_val) }
            }

            hir::ExprKind::ArrayRepeat { value, count } => {
                // Array repeat: evaluate value and count
                self.lower_expr(*value);
                self.lower_expr(*count);
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: expr.ty.clone(),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::InfiniteLoop { label, body } => {
                // Create loop basic blocks
                let loop_header = self.alloc_block(SmolStr::new("loop_header"));
                let loop_body = self.alloc_block(SmolStr::new("loop_body"));
                let loop_exit = self.alloc_block(SmolStr::new("loop_exit"));

                // Push loop onto stack for break/continue resolution
                self.loop_stack.push((label.clone(), loop_header, loop_exit));

                self.terminate(Terminator::Goto(loop_header));

                self.current_block = Some(loop_header);
                self.terminate(Terminator::Goto(loop_body));

                self.current_block = Some(loop_body);
                self.lower_body(body);
                self.terminate(Terminator::Goto(loop_header));

                // Pop loop from stack
                self.loop_stack.pop();

                self.current_block = Some(loop_exit);
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::ReturnExpr(opt_expr) => {
                let value = opt_expr.map(|e| self.lower_expr(e));
                self.terminate(Terminator::Return(value));
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::BreakExpr { label, value } => {
                // Evaluate break value if present (for side effects)
                if let Some(val_expr) = value {
                    self.lower_expr(*val_expr);
                }
                // Find the matching loop exit block on the stack
                let exit_block = self.find_loop_exit(label.as_ref());
                if let Some(exit) = exit_block {
                    self.terminate(Terminator::Goto(exit));
                    // Create a new unreachable block for any code after break
                    let dead_block = self.alloc_block(SmolStr::new("post_break_expr"));
                    self.current_block = Some(dead_block);
                }
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::ContinueExpr { label } => {
                // Find the matching loop header block on the stack
                let header_block = self.find_loop_header(label.as_ref());
                if let Some(header) = header_block {
                    self.terminate(Terminator::Goto(header));
                    // Create a new unreachable block for any code after continue
                    let dead_block = self.alloc_block(SmolStr::new("post_continue_expr"));
                    self.current_block = Some(dead_block);
                }
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ConstantKind::Unit,
                }))
            }

            hir::ExprKind::Lambda { params, body } => {
                // Generate a unique name for the lambda function
                let lambda_name = SmolStr::new(format!("__lambda_{}", self.lambda_counter));
                self.lambda_counter += 1;

                // Save the current lowering state
                let saved_function = self.current_function.take();
                let saved_block = self.current_block.take();
                let saved_local_map = std::mem::take(&mut self.local_map);
                let saved_next_local = self.next_local;
                self.next_local = 0;

                // Lower parameters for the lambda
                let mir_params: Vec<Local> = params
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

                // Create the lambda MIR function
                let lambda_func = Function {
                    span: expr.span,
                    name: lambda_name.clone(),
                    params: mir_params,
                    return_ty: expr.ty.clone(),
                    locals: Vec::new(),
                    basic_blocks: Arena::new(),
                    entry_block: BlockId::from_raw(la_arena::RawIdx::from_u32(0)),
                    resource_constraints: Vec::new(),
                    is_adaptive: false,
                };

                self.current_function = Some(lambda_func);

                // Create entry block for the lambda
                let entry = self.alloc_block(SmolStr::new("lambda_entry"));
                if let Some(func) = &mut self.current_function {
                    func.entry_block = entry;
                }
                self.current_block = Some(entry);

                // Lower the lambda body
                self.lower_body(body);

                // Extract the completed lambda function and add to MIR
                if let Some(lambda_fn) = self.current_function.take() {
                    self.mir.functions.push(lambda_fn);
                }

                // Restore the previous lowering state
                self.current_function = saved_function;
                self.current_block = saved_block;
                self.local_map = saved_local_map;
                self.next_local = saved_next_local;

                // Return a function reference constant
                Value::Constant(self.mir.constants.alloc(Constant {
                    ty: expr.ty.clone(),
                    kind: ConstantKind::Function(lambda_name),
                }))
            }

            hir::ExprKind::Struct { name, fields } => {
                // Lower struct construction: evaluate each field expression
                // Allocate a result temporary for the struct
                let result_local = self.next_local;
                self.next_local += 1;

                if let Some(f) = &mut self.current_function {
                    f.locals.push(Local {
                        id: result_local,
                        name: SmolStr::new(format!("struct_{}", name)),
                        ty: expr.ty.clone(),
                        mutable: false,
                    });
                }

                // Evaluate each field value and emit a Store for each field
                for (field_name, field_expr) in fields {
                    let field_val = self.lower_expr(*field_expr);
                    self.emit(expr.span, InstructionKind::Store {
                        ptr: Value::Field {
                            base: Box::new(Value::Local(result_local)),
                            field: field_name.clone(),
                        },
                        value: field_val,
                    });
                }

                Value::Local(result_local)
            }

            hir::ExprKind::Assign { target, value } => {
                // Lower assignment expression: evaluate value and assign to target local
                let mir_value = self.lower_expr(*value);
                if let Some(&mir_local) = self.local_map.get(target) {
                    self.emit(expr.span, InstructionKind::Assign {
                        target: mir_local,
                        value: mir_value,
                    });
                    Value::Local(mir_local)
                } else {
                    // Target local not found in map; return unit
                    Value::Constant(self.mir.constants.alloc(Constant {
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ConstantKind::Unit,
                    }))
                }
            }
        }
    }

    /// Find the exit block for a loop, matching by label if provided.
    /// Searches the loop stack from top (innermost) to bottom (outermost).
    fn find_loop_exit(&self, label: Option<&SmolStr>) -> Option<BlockId> {
        if let Some(lbl) = label {
            // Find by matching label
            for (loop_label, _header, exit) in self.loop_stack.iter().rev() {
                if loop_label.as_ref() == Some(lbl) {
                    return Some(*exit);
                }
            }
            None
        } else {
            // No label: use the innermost loop
            self.loop_stack.last().map(|(_, _, exit)| *exit)
        }
    }

    /// Find the header block for a loop, matching by label if provided.
    /// Searches the loop stack from top (innermost) to bottom (outermost).
    fn find_loop_header(&self, label: Option<&SmolStr>) -> Option<BlockId> {
        if let Some(lbl) = label {
            // Find by matching label
            for (loop_label, header, _exit) in self.loop_stack.iter().rev() {
                if loop_label.as_ref() == Some(lbl) {
                    return Some(*header);
                }
            }
            None
        } else {
            // No label: use the innermost loop
            self.loop_stack.last().map(|(_, header, _)| *header)
        }
    }

    fn lower_binary_op(&self, op: hir::BinaryOp) -> BinaryOp {
        match op {
            hir::BinaryOp::Add => BinaryOp::Add,
            hir::BinaryOp::Sub => BinaryOp::Sub,
            hir::BinaryOp::Mul => BinaryOp::Mul,
            hir::BinaryOp::Div => BinaryOp::Div,
            hir::BinaryOp::Rem => BinaryOp::Rem,
            hir::BinaryOp::Pow => BinaryOp::Pow,
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
