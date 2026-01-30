// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! HIR to MIR lowering.
//!
//! Transforms the high-level HIR into control-flow graph based MIR.

use crate::*;
use eclexia_hir as hir;
use rustc_hash::FxHashMap;

/// Lowering context for HIR → MIR transformation
pub struct LoweringContext {
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
}

impl LoweringContext {
    pub fn new() -> Self {
        Self {
            mir: MirFile::new(),
            current_function: None,
            local_map: FxHashMap::default(),
            next_local: 0,
            current_block: None,
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

        self.current_function = Some(mir_func.clone());

        // Create entry block
        let entry = self.alloc_block(SmolStr::new("entry"));
        mir_func.entry_block = entry;
        self.current_block = Some(entry);
        self.current_function = Some(mir_func);

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
        // This would access the HIR file, but we don't have it in scope
        // In a real implementation, we'd pass the HIR file to the context
        // For now, this is a placeholder
    }

    /// Lower an expression to a value
    fn lower_expr(&mut self, _expr_id: hir::ExprId) -> Value {
        // Placeholder - would lower HIR expressions to MIR values
        Value::Constant(self.mir.constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Unit),
            kind: ConstantKind::Unit,
        }))
    }
}

/// Lower a HIR file to MIR
pub fn lower_hir_file(hir: &hir::HirFile) -> MirFile {
    let mut ctx = LoweringContext::new();

    for item in &hir.items {
        ctx.lower_item(item);
    }

    ctx.mir
}
