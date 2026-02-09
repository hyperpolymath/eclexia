// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Compile-time evaluation for the Eclexia compiler.
//!
//! Provides:
//! - Constant folding on MIR (simplify known-value expressions)
//! - Compile-time expression evaluation
//! - Static resource budget verification
//!
//! The evaluator operates on MIR instructions and produces
//! simplified constants where possible.

pub mod const_fold;
pub mod resource_verify;

use eclexia_mir::ConstantKind;

/// Result of compile-time evaluation.
#[derive(Debug, Clone, PartialEq)]
pub enum ComptimeValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Char(char),
    Unit,
    /// Could not evaluate at compile time.
    Unknown,
}

impl ComptimeValue {
    /// Check if the value is statically known.
    pub fn is_known(&self) -> bool {
        !matches!(self, Self::Unknown)
    }

    /// Try to convert to a MIR constant kind.
    pub fn to_constant_kind(&self) -> Option<ConstantKind> {
        match self {
            Self::Int(v) => Some(ConstantKind::Int(*v)),
            Self::Float(v) => Some(ConstantKind::Float(*v)),
            Self::Bool(v) => Some(ConstantKind::Bool(*v)),
            Self::String(v) => Some(ConstantKind::String(v.as_str().into())),
            Self::Char(v) => Some(ConstantKind::Char(*v)),
            Self::Unit => Some(ConstantKind::Unit),
            Self::Unknown => None,
        }
    }

    /// Create from a MIR constant kind.
    pub fn from_constant_kind(kind: &ConstantKind) -> Self {
        match kind {
            ConstantKind::Int(v) => Self::Int(*v),
            ConstantKind::Float(v) => Self::Float(*v),
            ConstantKind::Bool(v) => Self::Bool(*v),
            ConstantKind::String(v) => Self::String(v.to_string()),
            ConstantKind::Char(v) => Self::Char(*v),
            ConstantKind::Unit => Self::Unit,
            ConstantKind::Resource { .. } | ConstantKind::Function(_) => Self::Unknown,
        }
    }
}

/// Result of a compile-time resource verification.
#[derive(Debug, Clone)]
pub enum ResourceVerification {
    /// Statically proved the constraint is satisfied.
    Proved {
        function: String,
        resource: String,
        constraint: String,
    },
    /// Statically proved the constraint is violated.
    Violated {
        function: String,
        resource: String,
        constraint: String,
        estimated_usage: f64,
        budget: f64,
    },
    /// Cannot determine statically; defer to runtime.
    Inconclusive {
        function: String,
        resource: String,
        reason: String,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comptime_value_known() {
        assert!(ComptimeValue::Int(42).is_known());
        assert!(ComptimeValue::Float(3.14).is_known());
        assert!(ComptimeValue::Bool(true).is_known());
        assert!(ComptimeValue::String("hello".to_string()).is_known());
        assert!(ComptimeValue::Unit.is_known());
        assert!(!ComptimeValue::Unknown.is_known());
    }

    #[test]
    fn test_comptime_value_roundtrip() {
        let val = ComptimeValue::Int(42);
        let kind = val.to_constant_kind().unwrap();
        let back = ComptimeValue::from_constant_kind(&kind);
        assert_eq!(val, back);
    }

    #[test]
    fn test_comptime_float_roundtrip() {
        let val = ComptimeValue::Float(2.718);
        let kind = val.to_constant_kind().unwrap();
        let back = ComptimeValue::from_constant_kind(&kind);
        assert_eq!(val, back);
    }

    #[test]
    fn test_unknown_has_no_constant() {
        assert!(ComptimeValue::Unknown.to_constant_kind().is_none());
    }
}
