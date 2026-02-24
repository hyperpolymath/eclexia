// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Abstract interpretation framework for Eclexia.
//!
//! Provides static analysis of MIR programs using abstract domains
//! to prove properties about resource consumption, value ranges,
//! and program correctness without executing the code.
//!
//! ## Domains
//!
//! - **Interval domain** — tracks numeric bounds `[lo, hi]`
//! - **Resource domain** — tracks cumulative resource usage bounds
//!
//! ## Analysis
//!
//! - **Resource analysis** — computes worst-case resource consumption
//!   per function, enabling compile-time budget verification
//! - **Transfer functions** — propagate abstract state through
//!   each MIR instruction kind

pub mod domains;
pub mod resource;
pub mod transfer;

/// Result of abstract resource analysis for a function.
#[derive(Debug, Clone)]
pub struct ResourceAnalysis {
    /// Function name.
    pub function: String,
    /// Per-resource usage bounds.
    pub resource_bounds: Vec<ResourceBound>,
}

/// Computed bound on a single resource dimension.
#[derive(Debug, Clone)]
pub struct ResourceBound {
    /// Resource name (e.g., "energy", "memory").
    pub resource: String,
    /// Minimum possible consumption.
    pub min_usage: f64,
    /// Maximum possible consumption.
    pub max_usage: f64,
}

impl ResourceBound {
    /// Check if a budget limit is definitely satisfied.
    pub fn definitely_within(&self, limit: f64) -> bool {
        self.max_usage <= limit
    }

    /// Check if a budget limit is definitely violated.
    pub fn definitely_exceeds(&self, limit: f64) -> bool {
        self.min_usage > limit
    }

    /// Check if a budget limit might or might not be satisfied.
    pub fn is_uncertain(&self, limit: f64) -> bool {
        self.min_usage <= limit && self.max_usage > limit
    }
}

/// Verification verdict for a resource budget.
#[derive(Debug, Clone, PartialEq)]
pub enum BudgetVerdict {
    /// Statically proved the budget is satisfied.
    Proved,
    /// Statically proved the budget is violated.
    Disproved {
        /// Minimum usage that exceeds the budget.
        min_usage: f64,
        /// The budget limit.
        limit: f64,
    },
    /// Cannot determine statically.
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resource_bound_within() {
        let bound = ResourceBound {
            resource: "energy".to_string(),
            min_usage: 20.0,
            max_usage: 80.0,
        };
        assert!(bound.definitely_within(100.0));
        assert!(!bound.definitely_within(50.0));
    }

    #[test]
    fn test_resource_bound_exceeds() {
        let bound = ResourceBound {
            resource: "energy".to_string(),
            min_usage: 120.0,
            max_usage: 200.0,
        };
        assert!(bound.definitely_exceeds(100.0));
        assert!(!bound.definitely_exceeds(150.0));
    }

    #[test]
    fn test_resource_bound_uncertain() {
        let bound = ResourceBound {
            resource: "energy".to_string(),
            min_usage: 80.0,
            max_usage: 120.0,
        };
        assert!(bound.is_uncertain(100.0));
        assert!(!bound.is_uncertain(200.0));
        assert!(!bound.is_uncertain(50.0));
    }

    #[test]
    fn test_budget_verdict_equality() {
        assert_eq!(BudgetVerdict::Proved, BudgetVerdict::Proved);
        assert_eq!(BudgetVerdict::Unknown, BudgetVerdict::Unknown);
        assert_ne!(BudgetVerdict::Proved, BudgetVerdict::Unknown);
    }
}
