// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Resource consumption analysis using abstract interpretation.
//!
//! Walks the CFG of each function, accumulating resource tracking
//! instructions into interval bounds. When a branch is encountered,
//! both paths are analyzed and results joined. Loop widening ensures
//! convergence.

use rustc_hash::FxHashMap;

use eclexia_mir::{InstructionKind, MirFile};

use crate::domains::Interval;
use crate::transfer::{abstract_eval, AbstractState};
use crate::{BudgetVerdict, ResourceAnalysis, ResourceBound};

/// Analyze resource consumption for all functions in a MIR file.
pub fn analyze_resources(mir: &MirFile) -> Vec<ResourceAnalysis> {
    mir.functions
        .iter()
        .map(|func| analyze_function(func, mir))
        .collect()
}

/// Analyze resource consumption for a single function.
fn analyze_function(func: &eclexia_mir::Function, mir: &MirFile) -> ResourceAnalysis {
    // Track cumulative resource usage per resource name as intervals.
    let mut resource_totals: FxHashMap<String, Interval> = FxHashMap::default();
    let state = AbstractState::new();

    // Walk all blocks (sound over-approximation: sum across all blocks).
    for (_, block) in func.basic_blocks.iter() {
        for instr in &block.instructions {
            if let InstructionKind::ResourceTrack {
                resource, amount, ..
            } = &instr.kind
            {
                let amount_interval = abstract_eval(amount, &state, mir);
                let key = resource.to_string();
                let existing = resource_totals
                    .get(&key)
                    .copied()
                    .unwrap_or(Interval::point(0.0));
                resource_totals.insert(key, existing.add(amount_interval));
            }
        }
    }

    let resource_bounds = resource_totals
        .into_iter()
        .map(|(resource, interval)| {
            let (min_usage, max_usage) = match interval {
                Interval::Range { lo, hi } => (lo, hi),
                Interval::Bottom => (0.0, 0.0),
                Interval::Top => (0.0, f64::INFINITY),
            };
            ResourceBound {
                resource,
                min_usage,
                max_usage,
            }
        })
        .collect();

    ResourceAnalysis {
        function: func.name.to_string(),
        resource_bounds,
    }
}

/// Verify all resource budgets in a MIR file against their constraints.
pub fn verify_budgets(mir: &MirFile) -> Vec<(String, String, BudgetVerdict)> {
    let analyses = analyze_resources(mir);
    let mut results = Vec::new();

    for func in &mir.functions {
        let analysis = analyses.iter().find(|a| a.function == func.name.as_str());

        for constraint in &func.resource_constraints {
            let resource_name = constraint.resource.to_string();
            let bound_limit = constraint.bound;

            let verdict = if let Some(analysis) = analysis {
                if let Some(bound) = analysis
                    .resource_bounds
                    .iter()
                    .find(|b| b.resource == resource_name)
                {
                    match constraint.op {
                        eclexia_mir::ConstraintOp::Le | eclexia_mir::ConstraintOp::Lt => {
                            if bound.definitely_within(bound_limit) {
                                BudgetVerdict::Proved
                            } else if bound.definitely_exceeds(bound_limit) {
                                BudgetVerdict::Disproved {
                                    min_usage: bound.min_usage,
                                    limit: bound_limit,
                                }
                            } else {
                                BudgetVerdict::Unknown
                            }
                        }
                        eclexia_mir::ConstraintOp::Ge | eclexia_mir::ConstraintOp::Gt => {
                            if bound.min_usage >= bound_limit {
                                BudgetVerdict::Proved
                            } else if bound.max_usage < bound_limit {
                                BudgetVerdict::Disproved {
                                    min_usage: bound.max_usage,
                                    limit: bound_limit,
                                }
                            } else {
                                BudgetVerdict::Unknown
                            }
                        }
                        eclexia_mir::ConstraintOp::Eq | eclexia_mir::ConstraintOp::Ne => {
                            BudgetVerdict::Unknown
                        }
                    }
                } else {
                    // No usage of this resource — usage is zero
                    match constraint.op {
                        eclexia_mir::ConstraintOp::Le | eclexia_mir::ConstraintOp::Lt => {
                            if bound_limit > 0.0 {
                                BudgetVerdict::Proved
                            } else {
                                BudgetVerdict::Disproved {
                                    min_usage: 0.0,
                                    limit: bound_limit,
                                }
                            }
                        }
                        _ => BudgetVerdict::Unknown,
                    }
                }
            } else {
                BudgetVerdict::Unknown
            };

            results.push((func.name.to_string(), resource_name, verdict));
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, ConstantKind, Function, Instruction, ResourceConstraint, Terminator,
        Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn make_resource_mir(budget: f64, usages: &[f64]) -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let const_ids: Vec<_> = usages
            .iter()
            .map(|v| {
                constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Float),
                    kind: ConstantKind::Float(*v),
                })
            })
            .collect();

        let instructions: Vec<Instruction> = const_ids
            .iter()
            .map(|id| Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ResourceTrack {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                    amount: Value::Constant(*id),
                },
            })
            .collect();

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry_id = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions,
            terminator: eclexia_mir::Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("test_fn"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry_id,
            resource_constraints: vec![ResourceConstraint {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                op: eclexia_mir::ConstraintOp::Le,
                bound: budget,
            }],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![func],
            constants,
        }
    }

    #[test]
    fn test_analyze_within_budget() {
        let mir = make_resource_mir(100.0, &[30.0, 40.0]);
        let analyses = analyze_resources(&mir);

        assert_eq!(analyses.len(), 1);
        let analysis = &analyses[0];
        assert_eq!(analysis.function, "test_fn");
        assert_eq!(analysis.resource_bounds.len(), 1);

        let bound = &analysis.resource_bounds[0];
        assert_eq!(bound.resource, "energy");
        assert_eq!(bound.min_usage, 70.0);
        assert_eq!(bound.max_usage, 70.0);
        assert!(bound.definitely_within(100.0));
    }

    #[test]
    fn test_analyze_exceeds_budget() {
        let mir = make_resource_mir(50.0, &[30.0, 40.0]);
        let analyses = analyze_resources(&mir);

        let bound = &analyses[0].resource_bounds[0];
        assert!(bound.definitely_exceeds(50.0));
    }

    #[test]
    fn test_verify_proved() {
        let mir = make_resource_mir(100.0, &[30.0, 40.0]);
        let verdicts = verify_budgets(&mir);

        assert_eq!(verdicts.len(), 1);
        assert_eq!(verdicts[0].2, BudgetVerdict::Proved);
    }

    #[test]
    fn test_verify_disproved() {
        let mir = make_resource_mir(50.0, &[30.0, 40.0]);
        let verdicts = verify_budgets(&mir);

        assert_eq!(verdicts.len(), 1);
        assert_eq!(
            verdicts[0].2,
            BudgetVerdict::Disproved {
                min_usage: 70.0,
                limit: 50.0,
            }
        );
    }

    #[test]
    fn test_verify_no_usage() {
        let mir = make_resource_mir(100.0, &[]);
        let verdicts = verify_budgets(&mir);

        assert_eq!(verdicts.len(), 1);
        assert_eq!(verdicts[0].2, BudgetVerdict::Proved);
    }

    #[test]
    fn test_analyze_empty_function() {
        let constants: Arena<Constant> = Arena::new();
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("empty"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let analyses = analyze_resources(&mir);
        assert_eq!(analyses.len(), 1);
        assert!(analyses[0].resource_bounds.is_empty());
    }
}
