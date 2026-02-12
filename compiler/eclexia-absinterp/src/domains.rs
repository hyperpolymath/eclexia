// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Abstract domains for static analysis.
//!
//! An abstract domain approximates concrete program values with a
//! lattice of abstract elements. The key domain here is the
//! **interval domain** which tracks numeric ranges `[lo, hi]`.

use std::fmt;

/// An interval `[lo, hi]` representing a range of possible values.
///
/// Invariant: `lo <= hi` when not bottom. `Bottom` represents
/// the empty set (unreachable state).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Interval {
    /// A concrete range `[lo, hi]`.
    Range { lo: f64, hi: f64 },
    /// The empty set — unreachable.
    Bottom,
    /// Any value — no information.
    Top,
}

impl Interval {
    /// Create a point interval `[v, v]`.
    pub fn point(v: f64) -> Self {
        Self::Range { lo: v, hi: v }
    }

    /// Create a range interval.
    pub fn range(lo: f64, hi: f64) -> Self {
        if lo > hi {
            Self::Bottom
        } else {
            Self::Range { lo, hi }
        }
    }

    /// Least upper bound (join) of two intervals.
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => Self::Range {
                lo: a.min(c),
                hi: b.max(d),
            },
        }
    }

    /// Greatest lower bound (meet) of two intervals.
    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) | (x, Self::Top) => x,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let lo = a.max(c);
                let hi = b.min(d);
                if lo > hi {
                    Self::Bottom
                } else {
                    Self::Range { lo, hi }
                }
            }
        }
    }

    /// Widen: accelerate convergence by pushing bounds toward infinity.
    pub fn widen(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) => x,
            (x, Self::Bottom) => x,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let lo = if c < a { f64::NEG_INFINITY } else { a };
                let hi = if d > b { f64::INFINITY } else { b };
                Self::Range { lo, hi }
            }
        }
    }

    /// Check if this interval is a subset of another.
    pub fn is_subset_of(self, other: Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) => true,
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (_, Self::Bottom) => false,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => a >= c && b <= d,
        }
    }

    /// Get the lower bound, if not bottom/top.
    pub fn lo(&self) -> Option<f64> {
        match self {
            Self::Range { lo, .. } => Some(*lo),
            _ => None,
        }
    }

    /// Get the upper bound, if not bottom/top.
    pub fn hi(&self) -> Option<f64> {
        match self {
            Self::Range { hi, .. } => Some(*hi),
            _ => None,
        }
    }

    /// Abstract addition.
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => Self::Range {
                lo: a + c,
                hi: b + d,
            },
        }
    }

    /// Abstract subtraction.
    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => Self::Range {
                lo: a - d,
                hi: b - c,
            },
        }
    }

    /// Abstract multiplication (handles sign combinations).
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let products = [a * c, a * d, b * c, b * d];
                let lo = products.iter().copied().fold(f64::INFINITY, f64::min);
                let hi = products.iter().copied().fold(f64::NEG_INFINITY, f64::max);
                Self::Range { lo, hi }
            }
        }
    }

    /// Abstract negation.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Top => Self::Top,
            Self::Range { lo, hi } => Self::Range { lo: -hi, hi: -lo },
        }
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "⊥"),
            Self::Top => write!(f, "⊤"),
            Self::Range { lo, hi } => {
                if (lo - hi).abs() < f64::EPSILON {
                    write!(f, "[{lo}]")
                } else {
                    write!(f, "[{lo}, {hi}]")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_interval() {
        let i = Interval::point(42.0);
        assert_eq!(i.lo(), Some(42.0));
        assert_eq!(i.hi(), Some(42.0));
    }

    #[test]
    fn test_range_interval() {
        let i = Interval::range(1.0, 10.0);
        assert_eq!(i.lo(), Some(1.0));
        assert_eq!(i.hi(), Some(10.0));
    }

    #[test]
    fn test_inverted_range_is_bottom() {
        let i = Interval::range(10.0, 1.0);
        assert_eq!(i, Interval::Bottom);
    }

    #[test]
    fn test_join() {
        let a = Interval::range(1.0, 5.0);
        let b = Interval::range(3.0, 8.0);
        let j = a.join(b);
        assert_eq!(j, Interval::range(1.0, 8.0));
    }

    #[test]
    fn test_join_with_bottom() {
        let a = Interval::range(1.0, 5.0);
        assert_eq!(a.join(Interval::Bottom), a);
        assert_eq!(Interval::Bottom.join(a), a);
    }

    #[test]
    fn test_join_with_top() {
        let a = Interval::range(1.0, 5.0);
        assert_eq!(a.join(Interval::Top), Interval::Top);
    }

    #[test]
    fn test_meet() {
        let a = Interval::range(1.0, 5.0);
        let b = Interval::range(3.0, 8.0);
        assert_eq!(a.meet(b), Interval::range(3.0, 5.0));
    }

    #[test]
    fn test_meet_disjoint() {
        let a = Interval::range(1.0, 3.0);
        let b = Interval::range(5.0, 8.0);
        assert_eq!(a.meet(b), Interval::Bottom);
    }

    #[test]
    fn test_add() {
        let a = Interval::range(1.0, 3.0);
        let b = Interval::range(10.0, 20.0);
        assert_eq!(a.add(b), Interval::range(11.0, 23.0));
    }

    #[test]
    fn test_sub() {
        let a = Interval::range(5.0, 10.0);
        let b = Interval::range(1.0, 3.0);
        assert_eq!(a.sub(b), Interval::range(2.0, 9.0));
    }

    #[test]
    fn test_mul_positive() {
        let a = Interval::range(2.0, 3.0);
        let b = Interval::range(4.0, 5.0);
        assert_eq!(a.mul(b), Interval::range(8.0, 15.0));
    }

    #[test]
    fn test_mul_mixed_signs() {
        let a = Interval::range(-2.0, 3.0);
        let b = Interval::range(-1.0, 4.0);
        let result = a.mul(b);
        // products: (-2)*(-1)=2, (-2)*4=-8, 3*(-1)=-3, 3*4=12
        assert_eq!(result, Interval::range(-8.0, 12.0));
    }

    #[test]
    fn test_neg() {
        let a = Interval::range(2.0, 5.0);
        assert_eq!(a.neg(), Interval::range(-5.0, -2.0));
    }

    #[test]
    fn test_widen() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(-1.0, 15.0);
        let w = a.widen(b);
        // b.lo < a.lo → push to -∞, b.hi > a.hi → push to +∞
        assert_eq!(
            w,
            Interval::Range {
                lo: f64::NEG_INFINITY,
                hi: f64::INFINITY
            }
        );
    }

    #[test]
    fn test_widen_no_change() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(2.0, 8.0);
        let w = a.widen(b);
        // b is contained in a — no widening needed
        assert_eq!(w, Interval::range(0.0, 10.0));
    }

    #[test]
    fn test_subset() {
        let a = Interval::range(2.0, 5.0);
        let b = Interval::range(1.0, 8.0);
        assert!(a.is_subset_of(b));
        assert!(!b.is_subset_of(a));
    }

    #[test]
    fn test_bottom_is_subset_of_anything() {
        assert!(Interval::Bottom.is_subset_of(Interval::range(0.0, 1.0)));
        assert!(Interval::Bottom.is_subset_of(Interval::Top));
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Interval::point(5.0)), "[5]");
        assert_eq!(format!("{}", Interval::range(1.0, 10.0)), "[1, 10]");
        assert_eq!(format!("{}", Interval::Bottom), "⊥");
        assert_eq!(format!("{}", Interval::Top), "⊤");
    }
}
