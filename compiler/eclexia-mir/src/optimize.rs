// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! MIR optimization passes.
//!
//! Implements various optimization transformations on MIR.

use crate::*;
use rustc_hash::FxHashSet;

/// Optimization level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationLevel {
    None,
    Basic,
    Aggressive,
}

/// Run optimization passes on MIR
pub fn optimize(mir: &mut MirFile, level: OptimizationLevel) {
    match level {
        OptimizationLevel::None => {}
        OptimizationLevel::Basic => {
            for func in &mut mir.functions {
                remove_nops(func);
                dead_code_elimination(func);
            }
        }
        OptimizationLevel::Aggressive => {
            for func in &mut mir.functions {
                remove_nops(func);
                dead_code_elimination(func);
                constant_propagation(func, &mir.constants);
                inline_small_blocks(func);
            }
        }
    }
}

/// Remove no-op instructions
fn remove_nops(func: &mut Function) {
    for block in func.basic_blocks.iter_mut() {
        block.1.instructions.retain(|inst| {
            !matches!(inst.kind, InstructionKind::Nop)
        });
    }
}

/// Dead code elimination
fn dead_code_elimination(func: &mut Function) {
    // Mark all reachable blocks
    let mut reachable = FxHashSet::default();
    let mut worklist = vec![func.entry_block];

    while let Some(block_id) = worklist.pop() {
        if reachable.insert(block_id) {
            let block = &func.basic_blocks[block_id];
            match &block.terminator {
                Terminator::Goto(target) => {
                    worklist.push(*target);
                }
                Terminator::Branch { then_block, else_block, .. } => {
                    worklist.push(*then_block);
                    worklist.push(*else_block);
                }
                Terminator::Switch { targets, default, .. } => {
                    for (_, target) in targets {
                        worklist.push(*target);
                    }
                    worklist.push(*default);
                }
                _ => {}
            }
        }
    }

    // Remove unreachable blocks (in a real implementation)
    // For now, just mark them with unreachable terminator
    for (block_id, block) in func.basic_blocks.iter_mut() {
        if !reachable.contains(&block_id) {
            block.instructions.clear();
            block.terminator = Terminator::Unreachable;
        }
    }
}

/// Constant propagation
fn constant_propagation(func: &mut Function, _constants: &Arena<Constant>) {
    use rustc_hash::FxHashMap;

    // Track local variables that hold constant values
    let mut const_locals: FxHashMap<LocalId, ConstantId> = FxHashMap::default();

    // Analyze instructions to find locals assigned to constants
    for block in func.basic_blocks.iter() {
        for inst in &block.1.instructions {
            if let InstructionKind::Assign { target, value } = &inst.kind {
                if let Value::Constant(const_id) = value {
                    const_locals.insert(*target, *const_id);
                }
            }
        }
    }

    // Propagate constants: replace local reads with constant values
    for block in func.basic_blocks.iter_mut() {
        for inst in &mut block.1.instructions {
            match &mut inst.kind {
                InstructionKind::Assign { value, .. } => {
                    replace_locals_with_constants(value, &const_locals);
                }
                InstructionKind::ResourceTrack { amount, .. } => {
                    replace_locals_with_constants(amount, &const_locals);
                }
                _ => {}
            }
        }

        // Also propagate in terminator
        match &mut block.1.terminator {
            Terminator::Branch { condition, .. } => {
                replace_locals_with_constants(condition, &const_locals);
            }
            Terminator::Switch { value, .. } => {
                replace_locals_with_constants(value, &const_locals);
            }
            Terminator::Return(Some(value)) => {
                replace_locals_with_constants(value, &const_locals);
            }
            _ => {}
        }
    }
}

/// Replace local variable reads with their constant values if known
fn replace_locals_with_constants(value: &mut Value, const_locals: &rustc_hash::FxHashMap<LocalId, ConstantId>) {
    match value {
        Value::Local(local_id) => {
            // If this local holds a constant, replace it
            if let Some(&const_id) = const_locals.get(local_id) {
                *value = Value::Constant(const_id);
            }
        }
        Value::Binary { lhs, rhs, .. } => {
            replace_locals_with_constants(lhs, const_locals);
            replace_locals_with_constants(rhs, const_locals);
        }
        Value::Unary { operand, .. } => {
            replace_locals_with_constants(operand, const_locals);
        }
        Value::Load { ptr } => {
            replace_locals_with_constants(ptr, const_locals);
        }
        Value::Field { base, .. } => {
            replace_locals_with_constants(base, const_locals);
        }
        Value::Index { base, index } => {
            replace_locals_with_constants(base, const_locals);
            replace_locals_with_constants(index, const_locals);
        }
        Value::Cast { value: inner, .. } => {
            replace_locals_with_constants(inner, const_locals);
        }
        _ => {}
    }
}

/// Inline small blocks
fn inline_small_blocks(func: &mut Function) {
    // Find blocks that only contain a goto (can be inlined into predecessors)
    let mut inline_candidates = FxHashSet::default();

    for (block_id, block) in func.basic_blocks.iter() {
        // A block can be inlined if it:
        // 1. Only has a Goto terminator
        // 2. Has few instructions (or zero)
        // 3. Is not the entry block
        if block_id != func.entry_block
            && block.instructions.len() <= 2
            && matches!(block.terminator, Terminator::Goto(_))
        {
            inline_candidates.insert(block_id);
        }
    }

    // Inline the candidates by redirecting predecessors
    for block_id in inline_candidates.clone() {
        let (target, instructions) = {
            let block = &func.basic_blocks[block_id];
            let target = match block.terminator {
                Terminator::Goto(t) => t,
                _ => continue,
            };
            (target, block.instructions.clone())
        };

        // Find all blocks that jump to this one and redirect them
        for (_, pred_block) in func.basic_blocks.iter_mut() {
            match &mut pred_block.terminator {
                Terminator::Goto(dest) if *dest == block_id => {
                    // Append this block's instructions to predecessor
                    pred_block.instructions.extend(instructions.clone());
                    // Redirect to the target
                    *dest = target;
                }
                Terminator::Branch {
                    then_block,
                    else_block,
                    ..
                } => {
                    if *then_block == block_id {
                        pred_block.instructions.extend(instructions.clone());
                        *then_block = target;
                    }
                    if *else_block == block_id {
                        pred_block.instructions.extend(instructions.clone());
                        *else_block = target;
                    }
                }
                Terminator::Switch { targets, default, .. } => {
                    for (_, dest) in targets.iter_mut() {
                        if *dest == block_id {
                            *dest = target;
                        }
                    }
                    if *default == block_id {
                        *default = target;
                    }
                }
                _ => {}
            }
        }
    }

    // Mark inlined blocks as unreachable (they'll be removed by DCE)
    for block_id in inline_candidates {
        let block = &mut func.basic_blocks[block_id];
        block.instructions.clear();
        block.terminator = Terminator::Unreachable;
    }
}

/// Optimize resource tracking
pub fn optimize_resource_tracking(func: &mut Function) {
    // Combine consecutive resource tracking operations
    for block in func.basic_blocks.iter_mut() {
        let mut new_instructions = Vec::new();
        let mut pending_resources: FxHashMap<SmolStr, (Dimension, Vec<Value>)> = FxHashMap::default();

        for inst in block.1.instructions.drain(..) {
            match &inst.kind {
                InstructionKind::ResourceTrack { resource, dimension, amount } => {
                    // Accumulate resource tracking
                    pending_resources
                        .entry(resource.clone())
                        .or_insert_with(|| (*dimension, Vec::new()))
                        .1
                        .push(amount.clone());
                }
                _ => {
                    // Flush pending resources
                    for (resource, (dimension, amounts)) in pending_resources.drain() {
                        if amounts.len() == 1 {
                            new_instructions.push(Instruction {
                                span: inst.span,
                                kind: InstructionKind::ResourceTrack {
                                    resource: resource.clone(),
                                    dimension,
                                    amount: amounts[0].clone(),
                                },
                            });
                        } else if !amounts.is_empty() {
                            // Combine multiple tracking operations
                            let combined = amounts.into_iter().reduce(|acc, val| {
                                Value::Binary {
                                    op: BinaryOp::Add,
                                    lhs: Box::new(acc),
                                    rhs: Box::new(val),
                                }
                            }).unwrap();

                            new_instructions.push(Instruction {
                                span: inst.span,
                                kind: InstructionKind::ResourceTrack {
                                    resource,
                                    dimension,
                                    amount: combined,
                                },
                            });
                        }
                    }

                    new_instructions.push(inst);
                }
            }
        }

        // Flush any remaining resources
        for (resource, (dimension, amounts)) in pending_resources.drain() {
            if !amounts.is_empty() {
                let combined = amounts.into_iter().reduce(|acc, val| {
                    Value::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(acc),
                        rhs: Box::new(val),
                    }
                }).unwrap();

                new_instructions.push(Instruction {
                    span: Span::default(),
                    kind: InstructionKind::ResourceTrack {
                        resource,
                        dimension,
                        amount: combined,
                    },
                });
            }
        }

        block.1.instructions = new_instructions;
    }
}

/// Insert shadow price hooks for adaptive functions
pub fn insert_shadow_price_hooks(func: &mut Function) {
    if !func.is_adaptive {
        return;
    }

    // Insert hooks at the entry of adaptive functions
    let entry_block = func.entry_block;
    let entry = &mut func.basic_blocks[entry_block];

    // Insert shadow price checks for each resource constraint
    for constraint in &func.resource_constraints {
        entry.instructions.insert(
            0,
            Instruction {
                span: Span::default(),
                kind: InstructionKind::ShadowPriceHook {
                    resource: constraint.resource.clone(),
                    dimension: constraint.dimension,
                },
            },
        );
    }
}
