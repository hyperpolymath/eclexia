// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Constant folding pass on MIR.
//!
//! Evaluates expressions with all-constant operands at compile time,
//! replacing them with their computed results. This reduces runtime
//! work and enables further optimizations.

use rustc_hash::FxHashMap;

use eclexia_mir::{BinaryOp, MirFile, UnaryOp, Value};

use crate::ComptimeValue;

/// Constant folding analysis over a MIR file.
///
/// Identifies which instructions could be folded to constants.
/// Returns the number of foldable instructions found.
pub fn analyze_foldable(mir: &MirFile) -> usize {
    let mut total = 0;

    for func in &mir.functions {
        let mut known_locals: FxHashMap<u32, ComptimeValue> = FxHashMap::default();

        for (_, block) in func.basic_blocks.iter() {
            for instr in &block.instructions {
                if let eclexia_mir::InstructionKind::Assign { target, value } = &instr.kind {
                    if let Some(folded) = try_fold_value(value, &known_locals, mir) {
                        known_locals.insert(*target, folded);
                        total += 1;
                    }
                }
            }
        }
    }

    total
}

/// Try to evaluate a MIR value at compile time.
pub fn try_fold_value(
    value: &Value,
    known_locals: &FxHashMap<u32, ComptimeValue>,
    mir: &MirFile,
) -> Option<ComptimeValue> {
    match value {
        Value::Constant(id) => {
            let constant = &mir.constants[*id];
            Some(ComptimeValue::from_constant_kind(&constant.kind))
        }
        Value::Local(id) => known_locals.get(id).cloned(),
        Value::Binary { op, lhs, rhs } => {
            let lhs_val = try_fold_value(lhs, known_locals, mir)?;
            let rhs_val = try_fold_value(rhs, known_locals, mir)?;
            fold_binary(*op, &lhs_val, &rhs_val)
        }
        Value::Unary { op, operand } => {
            let operand_val = try_fold_value(operand, known_locals, mir)?;
            fold_unary(*op, &operand_val)
        }
        _ => None,
    }
}

/// Evaluate a binary operation on compile-time values.
pub fn fold_binary(
    op: BinaryOp,
    lhs: &ComptimeValue,
    rhs: &ComptimeValue,
) -> Option<ComptimeValue> {
    match (op, lhs, rhs) {
        // Integer arithmetic
        (BinaryOp::Add, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            a.checked_add(*b).map(ComptimeValue::Int)
        }
        (BinaryOp::Sub, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            a.checked_sub(*b).map(ComptimeValue::Int)
        }
        (BinaryOp::Mul, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            a.checked_mul(*b).map(ComptimeValue::Int)
        }
        (BinaryOp::Div, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            if *b == 0 {
                None
            } else {
                a.checked_div(*b).map(ComptimeValue::Int)
            }
        }
        (BinaryOp::Rem, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            if *b == 0 {
                None
            } else {
                a.checked_rem(*b).map(ComptimeValue::Int)
            }
        }
        (BinaryOp::Pow, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            if *b >= 0 && *b <= u32::MAX as i64 {
                a.checked_pow(*b as u32).map(ComptimeValue::Int)
            } else {
                None
            }
        }

        // Float arithmetic
        (BinaryOp::Add, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            Some(ComptimeValue::Float(a + b))
        }
        (BinaryOp::Sub, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            Some(ComptimeValue::Float(a - b))
        }
        (BinaryOp::Mul, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            Some(ComptimeValue::Float(a * b))
        }
        (BinaryOp::Div, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            if *b == 0.0 {
                None
            } else {
                Some(ComptimeValue::Float(a / b))
            }
        }
        (BinaryOp::Rem, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            if *b == 0.0 {
                None
            } else {
                Some(ComptimeValue::Float(a % b))
            }
        }
        (BinaryOp::Pow, ComptimeValue::Float(a), ComptimeValue::Float(b)) => {
            Some(ComptimeValue::Float(a.powf(*b)))
        }

        // Integer comparisons
        (BinaryOp::Eq, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a == b))
        }
        (BinaryOp::Ne, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a != b))
        }
        (BinaryOp::Lt, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a < b))
        }
        (BinaryOp::Le, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a <= b))
        }
        (BinaryOp::Gt, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a > b))
        }
        (BinaryOp::Ge, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Bool(a >= b))
        }

        // Boolean operations
        (BinaryOp::And, ComptimeValue::Bool(a), ComptimeValue::Bool(b)) => {
            Some(ComptimeValue::Bool(*a && *b))
        }
        (BinaryOp::Or, ComptimeValue::Bool(a), ComptimeValue::Bool(b)) => {
            Some(ComptimeValue::Bool(*a || *b))
        }

        // Bitwise operations on integers
        (BinaryOp::BitAnd, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Int(a & b))
        }
        (BinaryOp::BitOr, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Int(a | b))
        }
        (BinaryOp::BitXor, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            Some(ComptimeValue::Int(a ^ b))
        }
        (BinaryOp::Shl, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            if *b >= 0 && *b < 64 {
                a.checked_shl(*b as u32).map(ComptimeValue::Int)
            } else {
                None
            }
        }
        (BinaryOp::Shr, ComptimeValue::Int(a), ComptimeValue::Int(b)) => {
            if *b >= 0 && *b < 64 {
                a.checked_shr(*b as u32).map(ComptimeValue::Int)
            } else {
                None
            }
        }

        // String concatenation
        (BinaryOp::Add, ComptimeValue::String(a), ComptimeValue::String(b)) => {
            Some(ComptimeValue::String(format!("{a}{b}")))
        }

        _ => None,
    }
}

/// Evaluate a unary operation on compile-time values.
pub fn fold_unary(op: UnaryOp, operand: &ComptimeValue) -> Option<ComptimeValue> {
    match (op, operand) {
        (UnaryOp::Neg, ComptimeValue::Int(v)) => Some(ComptimeValue::Int(-v)),
        (UnaryOp::Neg, ComptimeValue::Float(v)) => Some(ComptimeValue::Float(-v)),
        (UnaryOp::Not, ComptimeValue::Bool(v)) => Some(ComptimeValue::Bool(!v)),
        (UnaryOp::BitNot, ComptimeValue::Int(v)) => Some(ComptimeValue::Int(!v)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fold_int_arithmetic() {
        assert_eq!(
            fold_binary(BinaryOp::Add, &ComptimeValue::Int(3), &ComptimeValue::Int(4)),
            Some(ComptimeValue::Int(7))
        );
        assert_eq!(
            fold_binary(BinaryOp::Mul, &ComptimeValue::Int(5), &ComptimeValue::Int(6)),
            Some(ComptimeValue::Int(30))
        );
        assert_eq!(
            fold_binary(BinaryOp::Sub, &ComptimeValue::Int(10), &ComptimeValue::Int(3)),
            Some(ComptimeValue::Int(7))
        );
    }

    #[test]
    fn test_fold_div_by_zero() {
        assert_eq!(
            fold_binary(BinaryOp::Div, &ComptimeValue::Int(10), &ComptimeValue::Int(0)),
            None
        );
        assert_eq!(
            fold_binary(
                BinaryOp::Div,
                &ComptimeValue::Float(10.0),
                &ComptimeValue::Float(0.0)
            ),
            None
        );
    }

    #[test]
    fn test_fold_float_arithmetic() {
        assert_eq!(
            fold_binary(
                BinaryOp::Add,
                &ComptimeValue::Float(1.5),
                &ComptimeValue::Float(2.5)
            ),
            Some(ComptimeValue::Float(4.0))
        );
    }

    #[test]
    fn test_fold_comparisons() {
        assert_eq!(
            fold_binary(BinaryOp::Lt, &ComptimeValue::Int(3), &ComptimeValue::Int(5)),
            Some(ComptimeValue::Bool(true))
        );
        assert_eq!(
            fold_binary(BinaryOp::Eq, &ComptimeValue::Int(3), &ComptimeValue::Int(3)),
            Some(ComptimeValue::Bool(true))
        );
        assert_eq!(
            fold_binary(BinaryOp::Gt, &ComptimeValue::Int(3), &ComptimeValue::Int(5)),
            Some(ComptimeValue::Bool(false))
        );
    }

    #[test]
    fn test_fold_boolean_ops() {
        assert_eq!(
            fold_binary(
                BinaryOp::And,
                &ComptimeValue::Bool(true),
                &ComptimeValue::Bool(false)
            ),
            Some(ComptimeValue::Bool(false))
        );
        assert_eq!(
            fold_binary(
                BinaryOp::Or,
                &ComptimeValue::Bool(true),
                &ComptimeValue::Bool(false)
            ),
            Some(ComptimeValue::Bool(true))
        );
    }

    #[test]
    fn test_fold_unary() {
        assert_eq!(
            fold_unary(UnaryOp::Neg, &ComptimeValue::Int(5)),
            Some(ComptimeValue::Int(-5))
        );
        assert_eq!(
            fold_unary(UnaryOp::Not, &ComptimeValue::Bool(true)),
            Some(ComptimeValue::Bool(false))
        );
        assert_eq!(
            fold_unary(UnaryOp::Neg, &ComptimeValue::Float(3.14)),
            Some(ComptimeValue::Float(-3.14))
        );
    }

    #[test]
    fn test_fold_string_concat() {
        assert_eq!(
            fold_binary(
                BinaryOp::Add,
                &ComptimeValue::String("hello ".to_string()),
                &ComptimeValue::String("world".to_string())
            ),
            Some(ComptimeValue::String("hello world".to_string()))
        );
    }

    #[test]
    fn test_fold_mixed_types_returns_none() {
        assert_eq!(
            fold_binary(
                BinaryOp::Add,
                &ComptimeValue::Int(1),
                &ComptimeValue::Float(2.0)
            ),
            None
        );
    }

    #[test]
    fn test_fold_overflow_returns_none() {
        assert_eq!(
            fold_binary(
                BinaryOp::Add,
                &ComptimeValue::Int(i64::MAX),
                &ComptimeValue::Int(1)
            ),
            None
        );
    }

    #[test]
    fn test_bitwise_ops() {
        assert_eq!(
            fold_binary(
                BinaryOp::BitAnd,
                &ComptimeValue::Int(0b1100),
                &ComptimeValue::Int(0b1010)
            ),
            Some(ComptimeValue::Int(0b1000))
        );
        assert_eq!(
            fold_binary(
                BinaryOp::BitOr,
                &ComptimeValue::Int(0b1100),
                &ComptimeValue::Int(0b1010)
            ),
            Some(ComptimeValue::Int(0b1110))
        );
        assert_eq!(
            fold_unary(UnaryOp::BitNot, &ComptimeValue::Int(0)),
            Some(ComptimeValue::Int(-1))
        );
    }
}
