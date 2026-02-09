// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Transfer functions for abstract interpretation.
//!
//! Each MIR instruction kind has a transfer function that maps
//! pre-state → post-state in the abstract domain. The transfer
//! functions here operate on interval-valued abstract states.

use rustc_hash::FxHashMap;

use eclexia_mir::{BinaryOp, ConstantKind, MirFile, UnaryOp, Value};

use crate::domains::Interval;

/// Abstract state: maps each local variable to an interval.
#[derive(Debug, Clone)]
pub struct AbstractState {
    /// Mapping from local variable ID to its abstract value.
    pub locals: FxHashMap<u32, Interval>,
}

impl AbstractState {
    /// Create an empty state (all variables unmapped = bottom).
    pub fn new() -> Self {
        Self {
            locals: FxHashMap::default(),
        }
    }

    /// Get the abstract value of a local, defaulting to Bottom.
    pub fn get(&self, local: u32) -> Interval {
        self.locals.get(&local).copied().unwrap_or(Interval::Bottom)
    }

    /// Set the abstract value of a local.
    pub fn set(&mut self, local: u32, value: Interval) {
        self.locals.insert(local, value);
    }

    /// Join two states (least upper bound of each variable).
    pub fn join(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (&local, &interval) in &other.locals {
            let existing = result.get(local);
            result.set(local, existing.join(interval));
        }
        result
    }

    /// Widen this state with respect to another.
    pub fn widen(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (&local, &interval) in &other.locals {
            let existing = result.get(local);
            result.set(local, existing.widen(interval));
        }
        result
    }

    /// Check if this state is a subset of another.
    pub fn is_subset_of(&self, other: &Self) -> bool {
        for (&local, &interval) in &self.locals {
            let other_interval = other.get(local);
            if !interval.is_subset_of(other_interval) {
                return false;
            }
        }
        true
    }
}

impl Default for AbstractState {
    fn default() -> Self {
        Self::new()
    }
}

/// Evaluate a MIR value in the abstract domain.
pub fn abstract_eval(value: &Value, state: &AbstractState, mir: &MirFile) -> Interval {
    match value {
        Value::Constant(id) => {
            let constant = &mir.constants[*id];
            match &constant.kind {
                ConstantKind::Int(v) => Interval::point(*v as f64),
                ConstantKind::Float(v) => Interval::point(*v),
                ConstantKind::Resource { value, .. } => Interval::point(*value),
                ConstantKind::Bool(_) | ConstantKind::String(_) | ConstantKind::Char(_) => {
                    Interval::Top
                }
                ConstantKind::Unit | ConstantKind::Function(_) => Interval::Bottom,
            }
        }
        Value::Local(id) => state.get(*id),
        Value::Binary { op, lhs, rhs } => {
            let l = abstract_eval(lhs, state, mir);
            let r = abstract_eval(rhs, state, mir);
            abstract_binary(*op, l, r)
        }
        Value::Unary { op, operand } => {
            let v = abstract_eval(operand, state, mir);
            abstract_unary(*op, v)
        }
        _ => Interval::Top,
    }
}

/// Abstract binary operation on intervals.
fn abstract_binary(op: BinaryOp, lhs: Interval, rhs: Interval) -> Interval {
    match op {
        BinaryOp::Add => lhs.add(rhs),
        BinaryOp::Sub => lhs.sub(rhs),
        BinaryOp::Mul => lhs.mul(rhs),
        BinaryOp::Div => {
            // Division: if divisor range contains zero, go to Top
            match (lhs, rhs) {
                (Interval::Bottom, _) | (_, Interval::Bottom) => Interval::Bottom,
                (_, Interval::Range { lo, hi }) if lo <= 0.0 && hi >= 0.0 => Interval::Top,
                (Interval::Range { lo: a, hi: b }, Interval::Range { lo: c, hi: d }) => {
                    let quotients = [a / c, a / d, b / c, b / d];
                    let lo = quotients.iter().copied().fold(f64::INFINITY, f64::min);
                    let hi = quotients
                        .iter()
                        .copied()
                        .fold(f64::NEG_INFINITY, f64::max);
                    Interval::Range { lo, hi }
                }
                _ => Interval::Top,
            }
        }
        // For comparisons, the result is boolean — not a numeric interval
        BinaryOp::Eq
        | BinaryOp::Ne
        | BinaryOp::Lt
        | BinaryOp::Le
        | BinaryOp::Gt
        | BinaryOp::Ge
        | BinaryOp::And
        | BinaryOp::Or => Interval::Top,
        // For bitwise / range ops, conservatively return Top
        BinaryOp::Rem
        | BinaryOp::Pow
        | BinaryOp::BitAnd
        | BinaryOp::BitOr
        | BinaryOp::BitXor
        | BinaryOp::Shl
        | BinaryOp::Shr
        | BinaryOp::Range
        | BinaryOp::RangeInclusive => Interval::Top,
    }
}

/// Abstract unary operation on intervals.
fn abstract_unary(op: UnaryOp, operand: Interval) -> Interval {
    match op {
        UnaryOp::Neg => operand.neg(),
        UnaryOp::Not | UnaryOp::BitNot => Interval::Top,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_state_get_default() {
        let state = AbstractState::new();
        assert_eq!(state.get(0), Interval::Bottom);
    }

    #[test]
    fn test_abstract_state_set_get() {
        let mut state = AbstractState::new();
        state.set(0, Interval::range(1.0, 10.0));
        assert_eq!(state.get(0), Interval::range(1.0, 10.0));
    }

    #[test]
    fn test_abstract_state_join() {
        let mut s1 = AbstractState::new();
        s1.set(0, Interval::range(1.0, 5.0));

        let mut s2 = AbstractState::new();
        s2.set(0, Interval::range(3.0, 8.0));
        s2.set(1, Interval::point(42.0));

        let joined = s1.join(&s2);
        assert_eq!(joined.get(0), Interval::range(1.0, 8.0));
        assert_eq!(joined.get(1), Interval::point(42.0));
    }

    #[test]
    fn test_abstract_state_subset() {
        let mut s1 = AbstractState::new();
        s1.set(0, Interval::range(2.0, 4.0));

        let mut s2 = AbstractState::new();
        s2.set(0, Interval::range(1.0, 5.0));

        assert!(s1.is_subset_of(&s2));
        assert!(!s2.is_subset_of(&s1));
    }

    #[test]
    fn test_abstract_binary_add() {
        let result = abstract_binary(
            BinaryOp::Add,
            Interval::range(1.0, 3.0),
            Interval::range(10.0, 20.0),
        );
        assert_eq!(result, Interval::range(11.0, 23.0));
    }

    #[test]
    fn test_abstract_binary_div_with_zero() {
        let result = abstract_binary(
            BinaryOp::Div,
            Interval::range(1.0, 10.0),
            Interval::range(-1.0, 1.0), // contains zero
        );
        assert_eq!(result, Interval::Top);
    }

    #[test]
    fn test_abstract_binary_div_safe() {
        let result = abstract_binary(
            BinaryOp::Div,
            Interval::range(10.0, 20.0),
            Interval::range(2.0, 5.0),
        );
        assert_eq!(result, Interval::range(2.0, 10.0));
    }

    #[test]
    fn test_abstract_unary_neg() {
        let result = abstract_unary(UnaryOp::Neg, Interval::range(2.0, 5.0));
        assert_eq!(result, Interval::range(-5.0, -2.0));
    }

    #[test]
    fn test_abstract_eval_constant() {
        use eclexia_ast::types::{PrimitiveTy, Ty};
        use eclexia_mir::{Constant, MirFile};
        use la_arena::Arena;

        let mut constants: Arena<Constant> = Arena::new();
        let id = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(42),
        });

        let mir = MirFile {
            functions: vec![],
            constants,
        };

        let state = AbstractState::new();
        let result = abstract_eval(&Value::Constant(id), &state, &mir);
        assert_eq!(result, Interval::point(42.0));
    }

    #[test]
    fn test_abstract_eval_local() {
        use eclexia_mir::MirFile;
        use la_arena::Arena;

        let mir = MirFile {
            functions: vec![],
            constants: Arena::new(),
        };

        let mut state = AbstractState::new();
        state.set(3, Interval::range(5.0, 15.0));

        let result = abstract_eval(&Value::Local(3), &state, &mir);
        assert_eq!(result, Interval::range(5.0, 15.0));
    }
}
