// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Partial evaluation and adaptive specialization for Eclexia.
//!
//! When resource constraints are known at compile time, adaptive
//! functions can be specialized to eliminate runtime dispatch.
//!
//! ## Key features
//!
//! - **Binding-time analysis** — classify values as static (compile-time
//!   known) or dynamic (runtime dependent)
//! - **Adaptive specialization** — select the optimal solution branch
//!   when constraints are statically resolvable
//! - **Dead solution elimination** — remove unreachable solution branches

pub mod binding_time;
pub mod residualize;

use smol_str::SmolStr;

/// Binding-time classification for a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingTime {
    /// Value is known at compile time.
    Static,
    /// Value depends on runtime input.
    Dynamic,
}

impl BindingTime {
    /// Combine two binding times (static + dynamic = dynamic).
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Static, Self::Static) => Self::Static,
            _ => Self::Dynamic,
        }
    }
}

/// Result of specializing an adaptive function.
#[derive(Debug, Clone)]
pub struct SpecializationResult {
    /// Original adaptive function name.
    pub function: SmolStr,
    /// Which solution was selected (if specialization succeeded).
    pub selected_solution: Option<SmolStr>,
    /// Solutions that were eliminated as unreachable.
    pub eliminated_solutions: Vec<SmolStr>,
    /// Whether specialization was successful (all constraints static).
    pub fully_specialized: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binding_time_join_static() {
        assert_eq!(BindingTime::Static.join(BindingTime::Static), BindingTime::Static);
    }

    #[test]
    fn test_binding_time_join_dynamic() {
        assert_eq!(BindingTime::Static.join(BindingTime::Dynamic), BindingTime::Dynamic);
        assert_eq!(BindingTime::Dynamic.join(BindingTime::Static), BindingTime::Dynamic);
        assert_eq!(BindingTime::Dynamic.join(BindingTime::Dynamic), BindingTime::Dynamic);
    }

    #[test]
    fn test_specialization_result() {
        let result = SpecializationResult {
            function: SmolStr::new("sort"),
            selected_solution: Some(SmolStr::new("quicksort")),
            eliminated_solutions: vec![SmolStr::new("mergesort")],
            fully_specialized: true,
        };
        assert!(result.fully_specialized);
        assert_eq!(result.selected_solution.as_deref(), Some("quicksort"));
        assert_eq!(result.eliminated_solutions.len(), 1);
    }
}
