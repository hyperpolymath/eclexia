// SPDX-License-Identifier: MPL-2.0
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

    /// Scale a cost by a non-negative repetition count `k` (ADR-001 `scale(k, c)`).
    ///
    /// This is deliberately *not* `mul` folded against `Self::point(k)`: `mul`'s
    /// four-product fold computes `0.0 * f64::INFINITY = NaN` at the `k = 0`,
    /// `c = ⊤` (or any infinite endpoint) boundary, silently corrupting any
    /// later `is_subset_of`/`join`/`meet` that touches the result. Here that
    /// boundary is handled explicitly: an operation executed zero times costs
    /// nothing, even if each execution is individually unbounded.
    ///
    /// `k` must be non-negative and finite (checked by `debug_assert` in debug
    /// builds).
    pub fn scale(self, k: f64) -> Self {
        debug_assert!(
            k >= 0.0 && k.is_finite(),
            "Interval::scale: scale factor must be non-negative and finite, got {k}"
        );
        match self {
            Self::Bottom => Self::Bottom,
            Self::Top => {
                if k == 0.0 {
                    Self::point(0.0)
                } else {
                    Self::Top
                }
            }
            Self::Range { lo, hi } => {
                if k == 0.0 {
                    Self::point(0.0)
                } else {
                    Self::Range {
                        lo: ext_mul(k, lo),
                        hi: ext_mul(k, hi),
                    }
                }
            }
        }
    }

    /// Cost of executing `self` (a per-iteration cost) across a loop with
    /// trip-count interval `t` (ADR-001 `repeat(c, t)`).
    ///
    /// Computes `[lo(t)·lo(c), hi(t)·hi(c)]` under the extended-real
    /// conventions `0 · ∞ = 0` and `k · ∞ = ∞` for `k > 0` — again, not
    /// expressible via `mul`'s fold for the same `NaN`-at-zero reason as
    /// `scale`. `repeat(c, ⊤) = ⊤` unless `c = [0, 0]`; symmetrically,
    /// `repeat(⊤, t) = ⊤` unless `t = [0, 0]` (a zero-trip-count loop costs
    /// nothing regardless of how unbounded its body is — this direction is
    /// not stated explicitly in the ADR but follows the same "executed zero
    /// times costs nothing" principle as `scale(0, ⊤) = [0, 0]`).
    pub fn repeat(self, t: Self) -> Self {
        match (self, t) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, Self::Range { lo, hi }) if lo == 0.0 && hi == 0.0 => Self::point(0.0),
            (Self::Range { lo, hi }, Self::Top) if lo == 0.0 && hi == 0.0 => Self::point(0.0),
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: c_lo, hi: c_hi }, Self::Range { lo: t_lo, hi: t_hi }) => {
                debug_assert!(
                    t_lo >= 0.0,
                    "Interval::repeat: trip-count lower bound must be non-negative, got {t_lo}"
                );
                Self::Range {
                    lo: ext_mul(t_lo, c_lo),
                    hi: ext_mul(t_hi, c_hi),
                }
            }
        }
    }

    /// Widen a cost interval toward a source-derived *landmark* rather than
    /// toward infinity (ADR-001 "Widening for loops").
    ///
    /// This is deliberately not `widen`: `widen` pushes an escaping lower
    /// bound to `-∞`, which is wrong for costs (never negative) and would
    /// make every widened cost vacuously `⊤`-like on the low end. Instead:
    ///
    /// * an escaping lower bound (`other.lo < self.lo`) clamps to `0.0`;
    /// * an escaping upper bound (`other.hi > self.hi`) widens to the least
    ///   value in `landmarks` that is `>= other.hi`, or to `+∞` if no
    ///   landmark is `>=` it.
    ///
    /// `landmarks` should hold the finite limits on this resource drawn from
    /// enclosing `@requires`/`@provides`/`with_budget` annotations in scope
    /// (ADR-001's `L(r)`) — collecting that set from the AST/HIR is later
    /// work; this function only consumes it. Non-finite entries (`NaN`,
    /// `±∞`) in `landmarks` are ignored so a stray non-landmark value can't
    /// silently make widening a no-op.
    pub fn widen_cost(self, other: Self, landmarks: &[f64]) -> Self {
        match (self, other) {
            (Self::Bottom, x) => x,
            (x, Self::Bottom) => x,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let lo = if c < a { 0.0 } else { a };
                let hi = if d > b {
                    landmarks
                        .iter()
                        .copied()
                        .filter(|l| l.is_finite() && *l >= d)
                        .fold(f64::INFINITY, f64::min)
                } else {
                    b
                };
                Self::Range { lo, hi }
            }
        }
    }
}

/// Extended-real multiplication where `0 · ∞ = 0` (ADR-001 "The cost
/// lattice"). Differs from IEEE-754 `f64` multiplication, which produces
/// `NaN` for `0.0 * f64::INFINITY` — exactly the silent corruption `scale`
/// and `repeat` exist to avoid.
fn ext_mul(a: f64, b: f64) -> f64 {
    if a == 0.0 || b == 0.0 {
        0.0
    } else {
        a * b
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

    // ---- scale ----

    #[test]
    fn test_scale_zero_top_is_zero_not_top() {
        // scale(0, ⊤) = [0, 0]: executed zero times costs nothing even if
        // each execution is unbounded.
        assert_eq!(Interval::Top.scale(0.0), Interval::point(0.0));
    }

    #[test]
    fn test_scale_positive_top_stays_top() {
        assert_eq!(Interval::Top.scale(3.0), Interval::Top);
    }

    #[test]
    fn test_scale_zero_on_infinite_endpoint_is_not_nan() {
        // The NaN trap: naive `k * hi` with k=0.0 and hi=∞ is NaN under
        // IEEE-754. scale must give [0, 0], not a NaN-poisoned range.
        let c = Interval::Range {
            lo: 5.0,
            hi: f64::INFINITY,
        };
        assert_eq!(c.scale(0.0), Interval::point(0.0));
    }

    #[test]
    fn test_scale_pointwise() {
        let c = Interval::range(2.0, 3.0);
        assert_eq!(c.scale(4.0), Interval::range(8.0, 12.0));
    }

    #[test]
    fn test_scale_bottom_stays_bottom() {
        assert_eq!(Interval::Bottom.scale(5.0), Interval::Bottom);
        assert_eq!(Interval::Bottom.scale(0.0), Interval::Bottom);
    }

    // ---- repeat ----

    #[test]
    fn test_repeat_basic() {
        let c = Interval::range(2.0, 3.0);
        let t = Interval::range(4.0, 5.0);
        assert_eq!(c.repeat(t), Interval::range(8.0, 15.0));
    }

    #[test]
    fn test_repeat_top_trip_count_is_top() {
        let c = Interval::range(1.0, 2.0);
        assert_eq!(c.repeat(Interval::Top), Interval::Top);
    }

    #[test]
    fn test_repeat_top_trip_count_zero_cost_is_zero() {
        // repeat([0,0], ⊤) = [0,0]: zero cost per iteration, however many
        // iterations, is still zero cost.
        assert_eq!(
            Interval::point(0.0).repeat(Interval::Top),
            Interval::point(0.0)
        );
    }

    #[test]
    fn test_repeat_top_cost_is_top() {
        assert_eq!(Interval::Top.repeat(Interval::range(1.0, 5.0)), Interval::Top);
    }

    #[test]
    fn test_repeat_top_cost_zero_trip_count_is_zero() {
        // repeat(⊤, [0,0]) = [0,0]: a loop that never runs costs nothing,
        // however unbounded its body is.
        assert_eq!(
            Interval::Top.repeat(Interval::point(0.0)),
            Interval::point(0.0)
        );
    }

    #[test]
    fn test_repeat_bottom_absorbs() {
        assert_eq!(
            Interval::Bottom.repeat(Interval::range(1.0, 2.0)),
            Interval::Bottom
        );
        assert_eq!(
            Interval::range(1.0, 2.0).repeat(Interval::Bottom),
            Interval::Bottom
        );
    }

    #[test]
    fn test_repeat_range_zero_trip_count_on_infinite_cost_is_not_nan() {
        // Same NaN trap as scale, but inside the Range/Range branch: cost
        // per iteration is [0, ∞] (a legitimate value, e.g. from
        // widen_cost's "no landmark" case), trip count is exactly [0, 0].
        // Naive `t_hi * c_hi` = 0.0 * ∞ = NaN under IEEE-754.
        let c = Interval::Range {
            lo: 0.0,
            hi: f64::INFINITY,
        };
        let t = Interval::point(0.0);
        assert_eq!(c.repeat(t), Interval::point(0.0));
    }

    #[test]
    fn test_repeat_range_positive_trip_count_on_infinite_cost_is_top_like() {
        let c = Interval::Range {
            lo: 0.0,
            hi: f64::INFINITY,
        };
        let t = Interval::range(0.0, 5.0);
        assert_eq!(
            c.repeat(t),
            Interval::Range {
                lo: 0.0,
                hi: f64::INFINITY
            }
        );
    }

    // ---- widen_cost ----

    #[test]
    fn test_widen_cost_lower_bound_clamps_to_zero_not_neg_infinity() {
        let a = Interval::range(2.0, 10.0);
        let b = Interval::range(-5.0, 10.0);
        assert_eq!(a.widen_cost(b, &[]), Interval::range(0.0, 10.0));
    }

    #[test]
    fn test_widen_cost_upper_bound_widens_to_least_landmark_ge_d() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(0.0, 15.0);
        let landmarks = [20.0, 50.0];
        assert_eq!(a.widen_cost(b, &landmarks), Interval::range(0.0, 20.0));
    }

    #[test]
    fn test_widen_cost_landmark_exactly_equal_to_d_is_picked() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(0.0, 15.0);
        let landmarks = [15.0];
        assert_eq!(a.widen_cost(b, &landmarks), Interval::range(0.0, 15.0));
    }

    #[test]
    fn test_widen_cost_no_landmark_at_or_above_d_widens_to_infinity() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(0.0, 15.0);
        let landmarks = [5.0]; // below d=15, so unusable
        assert_eq!(
            a.widen_cost(b, &landmarks),
            Interval::Range {
                lo: 0.0,
                hi: f64::INFINITY
            }
        );
    }

    #[test]
    fn test_widen_cost_picks_least_landmark_among_several() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(0.0, 15.0);
        let landmarks = [100.0, 20.0, 50.0];
        assert_eq!(a.widen_cost(b, &landmarks), Interval::range(0.0, 20.0));
    }

    #[test]
    fn test_widen_cost_no_change_when_other_is_subset() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(2.0, 8.0);
        // other ⊆ self: nothing escapes, so the chain does not advance —
        // this is what guarantees the widening sequence terminates.
        assert_eq!(a.widen_cost(b, &[1.0, 2.0]), a);
    }

    #[test]
    fn test_widen_cost_ignores_non_finite_landmarks() {
        let a = Interval::range(0.0, 10.0);
        let b = Interval::range(0.0, 15.0);
        let landmarks = [f64::INFINITY, f64::NAN, 25.0];
        assert_eq!(a.widen_cost(b, &landmarks), Interval::range(0.0, 25.0));
    }

    #[test]
    fn test_widen_cost_top_absorbs() {
        let a = Interval::range(1.0, 2.0);
        assert_eq!(Interval::Top.widen_cost(a, &[]), Interval::Top);
        assert_eq!(a.widen_cost(Interval::Top, &[]), Interval::Top);
    }

    #[test]
    fn test_widen_cost_bottom_is_identity() {
        let a = Interval::range(1.0, 2.0);
        assert_eq!(Interval::Bottom.widen_cost(a, &[]), a);
        assert_eq!(a.widen_cost(Interval::Bottom, &[]), a);
    }
}
