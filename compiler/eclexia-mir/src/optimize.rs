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
fn constant_propagation(_func: &mut Function, _constants: &Arena<Constant>) {
    // TODO: Implement constant propagation
    // This would track constant values and replace uses with constants
}

/// Inline small blocks
fn inline_small_blocks(_func: &mut Function) {
    // TODO: Implement block inlining
    // Merge blocks with only a goto terminator into their predecessors
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
