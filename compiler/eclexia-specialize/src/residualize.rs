// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Residual code generation for specialized adaptive functions.
//!
//! When an adaptive function's constraints are statically known,
//! this module selects the optimal solution and eliminates dead
//! solution branches, producing a specialized non-adaptive function.

use eclexia_comptime::const_fold::try_fold_value;
use eclexia_comptime::ComptimeValue;
use eclexia_mir::{ConstraintOp, MirFile, Solution};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::SpecializationResult;

/// Try to specialize an adaptive function by selecting the best solution.
///
/// If all resource constraints can be evaluated at compile time,
/// selects the first solution whose condition (if any) is satisfied.
pub fn try_specialize_adaptive(
    func: &eclexia_mir::AdaptiveFunction,
    mir: &MirFile,
) -> SpecializationResult {
    let known_locals: FxHashMap<u32, ComptimeValue> = FxHashMap::default();

    // Try to evaluate each solution's condition
    let mut selected: Option<SmolStr> = None;
    let mut eliminated: Vec<SmolStr> = Vec::new();

    for solution in &func.solutions {
        if let Some(condition) = &solution.condition {
            match try_fold_value(condition, &known_locals, mir) {
                Some(ComptimeValue::Bool(true)) => {
                    if selected.is_none() {
                        selected = Some(solution.name.clone());
                    } else {
                        // Already selected a solution — this one is redundant
                        eliminated.push(solution.name.clone());
                    }
                }
                Some(ComptimeValue::Bool(false)) => {
                    // Condition is statically false — eliminate
                    eliminated.push(solution.name.clone());
                }
                _ => {
                    // Can't determine — keep this solution
                    if selected.is_none() {
                        // Dynamic condition — can't fully specialize
                        return SpecializationResult {
                            function: func.name.clone(),
                            selected_solution: None,
                            eliminated_solutions: eliminated,
                            fully_specialized: false,
                        };
                    }
                }
            }
        } else {
            // Unconditional fallback solution
            if selected.is_none() {
                selected = Some(solution.name.clone());
            } else {
                eliminated.push(solution.name.clone());
            }
        }
    }

    let fully_specialized = selected.is_some();

    SpecializationResult {
        function: func.name.clone(),
        selected_solution: selected,
        eliminated_solutions: eliminated,
        fully_specialized,
    }
}

/// Check if a solution satisfies all resource constraints.
pub fn solution_satisfies_constraints(
    solution: &Solution,
    constraints: &[eclexia_mir::ResourceConstraint],
) -> Option<bool> {
    for constraint in constraints {
        let cost = solution
            .resource_costs
            .iter()
            .find(|c| c.resource == constraint.resource)?;

        let satisfied = match constraint.op {
            ConstraintOp::Le => cost.amount <= constraint.bound,
            ConstraintOp::Lt => cost.amount < constraint.bound,
            ConstraintOp::Ge => cost.amount >= constraint.bound,
            ConstraintOp::Gt => cost.amount > constraint.bound,
            ConstraintOp::Eq => (cost.amount - constraint.bound).abs() < f64::EPSILON,
            ConstraintOp::Ne => (cost.amount - constraint.bound).abs() >= f64::EPSILON,
        };

        if !satisfied {
            return Some(false);
        }
    }

    Some(true)
}

/// Select the best solution from an adaptive function based on
/// static resource costs and constraints.
pub fn select_best_solution<'a>(
    solutions: &'a [Solution],
    constraints: &[eclexia_mir::ResourceConstraint],
) -> Option<&'a Solution> {
    // Find the first solution that satisfies all constraints
    solutions
        .iter()
        .find(|s| solution_satisfies_constraints(s, constraints) == Some(true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_mir::{ResourceCost, ResourceConstraint, Solution};
    use smol_str::SmolStr;

    fn make_solution(name: &str, energy_cost: f64) -> Solution {
        Solution {
            name: SmolStr::new(name),
            condition: None,
            function: make_dummy_function(name),
            resource_costs: vec![ResourceCost {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                amount: energy_cost,
            }],
        }
    }

    fn make_dummy_function(name: &str) -> eclexia_mir::Function {
        use eclexia_ast::span::Span;
        use eclexia_ast::types::{PrimitiveTy, Ty};
        use la_arena::Arena;

        let mut basic_blocks: Arena<eclexia_mir::BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(eclexia_mir::BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: eclexia_mir::Terminator::Return(None),
        });

        eclexia_mir::Function {
            span: Span::new(0, 0),
            name: SmolStr::new(name),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        }
    }

    #[test]
    fn test_solution_satisfies_le_constraint() {
        let solution = make_solution("quicksort", 30.0);
        let constraints = vec![ResourceConstraint {
            resource: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            op: ConstraintOp::Le,
            bound: 50.0,
        }];

        assert_eq!(
            solution_satisfies_constraints(&solution, &constraints),
            Some(true)
        );
    }

    #[test]
    fn test_solution_violates_le_constraint() {
        let solution = make_solution("quicksort", 80.0);
        let constraints = vec![ResourceConstraint {
            resource: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            op: ConstraintOp::Le,
            bound: 50.0,
        }];

        assert_eq!(
            solution_satisfies_constraints(&solution, &constraints),
            Some(false)
        );
    }

    #[test]
    fn test_select_best_solution() {
        let solutions = vec![
            make_solution("quicksort", 80.0),
            make_solution("mergesort", 40.0),
            make_solution("bubblesort", 20.0),
        ];

        let constraints = vec![ResourceConstraint {
            resource: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            op: ConstraintOp::Le,
            bound: 50.0,
        }];

        let best = select_best_solution(&solutions, &constraints).unwrap();
        // quicksort (80) exceeds budget, mergesort (40) fits first
        assert_eq!(best.name, "mergesort");
    }

    #[test]
    fn test_select_best_no_solution() {
        let solutions = vec![
            make_solution("quicksort", 80.0),
            make_solution("mergesort", 60.0),
        ];

        let constraints = vec![ResourceConstraint {
            resource: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            op: ConstraintOp::Le,
            bound: 50.0,
        }];

        assert!(select_best_solution(&solutions, &constraints).is_none());
    }

    #[test]
    fn test_missing_resource_returns_none() {
        let solution = make_solution("quicksort", 30.0);
        let constraints = vec![ResourceConstraint {
            resource: SmolStr::new("memory"), // solution has "energy" not "memory"
            dimension: Dimension::dimensionless(),
            op: ConstraintOp::Le,
            bound: 50.0,
        }];

        assert_eq!(
            solution_satisfies_constraints(&solution, &constraints),
            None
        );
    }

    #[test]
    fn test_specialization_result_fields() {
        let result = SpecializationResult {
            function: SmolStr::new("sort"),
            selected_solution: Some(SmolStr::new("quicksort")),
            eliminated_solutions: vec![SmolStr::new("mergesort"), SmolStr::new("bubblesort")],
            fully_specialized: true,
        };

        assert!(result.fully_specialized);
        assert_eq!(result.eliminated_solutions.len(), 2);
    }
}
