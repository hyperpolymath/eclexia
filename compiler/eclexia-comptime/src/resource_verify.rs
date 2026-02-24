// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Static resource budget verification.
//!
//! Analyzes MIR functions to verify that resource constraints
//! (e.g., `@requires energy <= 100J`) can be statically proven.
//! When all resource usages in a function are compile-time constants,
//! we can verify the budget at compile time rather than runtime.

use eclexia_mir::{ConstantKind, ConstraintOp, InstructionKind, MirFile, Value};

use crate::ResourceVerification;

/// Verify all resource constraints in a MIR file.
///
/// Returns a verification result for each annotated function.
pub fn verify_resource_budgets(mir: &MirFile) -> Vec<ResourceVerification> {
    let mut results = Vec::new();

    for func in &mir.functions {
        results.extend(verify_function(func, mir));
    }

    results
}

/// Verify resource constraints for a single function.
fn verify_function(func: &eclexia_mir::Function, mir: &MirFile) -> Vec<ResourceVerification> {
    let mut results = Vec::new();

    // Collect resource tracking instructions
    let mut resource_usages: Vec<ResourceUsage> = Vec::new();

    for (_, block) in func.basic_blocks.iter() {
        for instr in &block.instructions {
            if let InstructionKind::ResourceTrack {
                resource, amount, ..
            } = &instr.kind
            {
                let static_amount = try_resolve_constant(amount, mir);
                resource_usages.push(ResourceUsage {
                    resource: resource.to_string(),
                    static_amount,
                });
            }
        }
    }

    // Check against declared constraints
    for constraint in &func.resource_constraints {
        let resource_name = constraint.resource.to_string();
        let budget_limit = constraint.bound;

        // Sum up all static usages for this resource
        let mut total_known: f64 = 0.0;
        let mut has_unknown = false;

        for usage in &resource_usages {
            if usage.resource == resource_name {
                match usage.static_amount {
                    Some(amount) => total_known += amount,
                    None => has_unknown = true,
                }
            }
        }

        if has_unknown {
            results.push(ResourceVerification::Inconclusive {
                function: func.name.to_string(),
                resource: resource_name,
                reason: "contains dynamic resource usage that cannot be statically resolved"
                    .to_string(),
            });
        } else if !check_constraint(total_known, constraint.op, budget_limit) {
            results.push(ResourceVerification::Violated {
                function: func.name.to_string(),
                resource: resource_name,
                constraint: format!("{} {budget_limit}", constraint_op_str(constraint.op)),
                estimated_usage: total_known,
                budget: budget_limit,
            });
        } else {
            results.push(ResourceVerification::Proved {
                function: func.name.to_string(),
                resource: resource_name,
                constraint: format!("{} {budget_limit}", constraint_op_str(constraint.op)),
            });
        }
    }

    results
}

/// Check if a value satisfies a constraint.
fn check_constraint(value: f64, op: ConstraintOp, bound: f64) -> bool {
    match op {
        ConstraintOp::Lt => value < bound,
        ConstraintOp::Le => value <= bound,
        ConstraintOp::Gt => value > bound,
        ConstraintOp::Ge => value >= bound,
        ConstraintOp::Eq => (value - bound).abs() < f64::EPSILON,
        ConstraintOp::Ne => (value - bound).abs() >= f64::EPSILON,
    }
}

/// Human-readable string for a constraint operator.
fn constraint_op_str(op: ConstraintOp) -> &'static str {
    match op {
        ConstraintOp::Lt => "<",
        ConstraintOp::Le => "<=",
        ConstraintOp::Gt => ">",
        ConstraintOp::Ge => ">=",
        ConstraintOp::Eq => "==",
        ConstraintOp::Ne => "!=",
    }
}

/// Intermediate representation of a resource usage.
struct ResourceUsage {
    resource: String,
    /// The amount, if statically resolvable.
    static_amount: Option<f64>,
}

/// Try to resolve a MIR value to a static float.
fn try_resolve_constant(value: &Value, mir: &MirFile) -> Option<f64> {
    match value {
        Value::Constant(id) => {
            let constant = &mir.constants[*id];
            match &constant.kind {
                ConstantKind::Int(v) => Some(*v as f64),
                ConstantKind::Float(v) => Some(*v),
                ConstantKind::Resource { value, .. } => Some(*value),
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, Function, Instruction, ResourceConstraint, Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn make_test_mir(budget_limit: f64, op: ConstraintOp, usage_amounts: &[f64]) -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();

        // Create constants for each usage amount
        let const_ids: Vec<_> = usage_amounts
            .iter()
            .map(|amount| {
                constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Float),
                    kind: ConstantKind::Float(*amount),
                })
            })
            .collect();

        // Create resource tracking instructions
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
            terminator: Terminator::Return(None),
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
                op,
                bound: budget_limit,
            }],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![func],
            constants,
        }
    }

    #[test]
    fn test_verify_within_budget() {
        let mir = make_test_mir(100.0, ConstraintOp::Le, &[30.0, 40.0]);
        let results = verify_resource_budgets(&mir);

        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], ResourceVerification::Proved { .. }));
    }

    #[test]
    fn test_verify_exceeds_budget() {
        let mir = make_test_mir(50.0, ConstraintOp::Le, &[30.0, 40.0]);
        let results = verify_resource_budgets(&mir);

        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], ResourceVerification::Violated { .. }));
        if let ResourceVerification::Violated {
            estimated_usage,
            budget,
            ..
        } = &results[0]
        {
            assert_eq!(*estimated_usage, 70.0);
            assert_eq!(*budget, 50.0);
        }
    }

    #[test]
    fn test_verify_exact_budget() {
        let mir = make_test_mir(70.0, ConstraintOp::Le, &[30.0, 40.0]);
        let results = verify_resource_budgets(&mir);

        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], ResourceVerification::Proved { .. }));
    }

    #[test]
    fn test_no_constraints_no_results() {
        let mut mir = make_test_mir(100.0, ConstraintOp::Le, &[50.0]);
        mir.functions[0].resource_constraints.clear();

        let results = verify_resource_budgets(&mir);
        assert!(results.is_empty());
    }

    #[test]
    fn test_constraint_op_check() {
        assert!(check_constraint(50.0, ConstraintOp::Le, 100.0));
        assert!(!check_constraint(150.0, ConstraintOp::Le, 100.0));
        assert!(check_constraint(50.0, ConstraintOp::Lt, 100.0));
        assert!(!check_constraint(100.0, ConstraintOp::Lt, 100.0));
        assert!(check_constraint(150.0, ConstraintOp::Gt, 100.0));
        assert!(!check_constraint(50.0, ConstraintOp::Gt, 100.0));
    }
}
