// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Cost-carrying effect rows (ADR-001 "Cost-carrying effect rows").
//!
//! [`Effects`] pairs an [`EffectRow`] (unchanged, see [`crate::row`]) with a
//! per-resource cost map. Cost lives on the row rather than being recovered
//! from the effect labels alone, because a label set is a set: two `Net`
//! operations cost twice what one costs, and the label set can't tell them
//! apart.
//!
//! ## The absent-key convention
//!
//! A cost is a *partial* map from resource name to [`Interval`]. Whether an
//! absent resource means "no usage" or "usage unknown" depends on whether
//! the row is open or closed — this is the load-bearing detail that a naive
//! implementation gets wrong (the "vacuity bug" the ADR names):
//!
//! * in a **closed** (or **pure**) cost, an absent resource means `[0, 0]`
//!   — genuinely no usage, since the row can't be extended with more
//!   effects (and therefore more cost) later;
//! * in an **open** cost, an absent resource means `⊤` — usage unknown,
//!   since the row variable could be instantiated with an effect that uses
//!   the resource.
//!
//! This module only defines the data type and `cost_of`; it is not wired
//! into the typechecker, interpreter, or verifier.

use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use eclexia_absinterp::domains::Interval;

use crate::row::EffectRow;

/// An effect row paired with a per-resource cost map.
///
/// Openness is *not* duplicated onto the cost map: it is read off `row` by
/// [`Effects::cost_of`] when a resource is absent from `cost`.
#[derive(Debug, Clone, PartialEq)]
pub struct Effects {
    row: EffectRow,
    cost: FxHashMap<SmolStr, Interval>,
}

impl Effects {
    /// Create an `Effects` with no recorded cost for any resource.
    ///
    /// `cost_of` on the result falls back to the row's absent-key
    /// convention: `[0, 0]` if `row` is closed/pure, `⊤` if `row` is open.
    pub fn new(row: EffectRow) -> Self {
        Self {
            row,
            cost: FxHashMap::default(),
        }
    }

    /// Record (or overwrite) the cost of resource `r`.
    pub fn with_cost(mut self, r: impl Into<SmolStr>, interval: Interval) -> Self {
        self.cost.insert(r.into(), interval);
        self
    }

    /// Record (or overwrite) the cost of resource `r`, in place.
    pub fn set_cost(&mut self, r: impl Into<SmolStr>, interval: Interval) {
        self.cost.insert(r.into(), interval);
    }

    /// The underlying effect row.
    pub fn row(&self) -> &EffectRow {
        &self.row
    }

    /// The cost of resource `r`.
    ///
    /// Looks `r` up in the explicit cost map first. If `r` is absent, falls
    /// back to the row's openness: `⊤` (unknown) for an open row, `[0, 0]`
    /// (no usage) for a closed or pure row.
    pub fn cost_of(&self, r: &str) -> Interval {
        self.cost.get(r).copied().unwrap_or(if self.row.is_open() {
            Interval::Top
        } else {
            Interval::point(0.0)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cost_of_explicit_entry_is_used_regardless_of_openness() {
        let closed = Effects::new(EffectRow::closed(vec![SmolStr::new("Net")]))
            .with_cost("time", Interval::range(1.0, 5.0));
        assert_eq!(closed.cost_of("time"), Interval::range(1.0, 5.0));

        let open = Effects::new(EffectRow::open(
            vec![SmolStr::new("Net")],
            SmolStr::new("r"),
        ))
        .with_cost("time", Interval::range(1.0, 5.0));
        assert_eq!(open.cost_of("time"), Interval::range(1.0, 5.0));
    }

    #[test]
    fn test_cost_of_absent_on_closed_row_is_zero() {
        let e = Effects::new(EffectRow::closed(vec![SmolStr::new("Console")]));
        assert_eq!(e.cost_of("energy"), Interval::point(0.0));
    }

    #[test]
    fn test_cost_of_absent_on_open_row_is_top() {
        let e = Effects::new(EffectRow::open(
            vec![SmolStr::new("Console")],
            SmolStr::new("r"),
        ));
        assert_eq!(e.cost_of("energy"), Interval::Top);
    }

    #[test]
    fn test_cost_of_absent_on_pure_row_is_zero_not_top() {
        // Pure is not open — a lazy `is_open()`-adjacent check (e.g.
        // "is this NOT Closed") would wrongly return ⊤ here.
        let e = Effects::new(EffectRow::pure());
        assert_eq!(e.cost_of("time"), Interval::point(0.0));
    }

    #[test]
    fn test_set_cost_mutates_in_place() {
        let mut e = Effects::new(EffectRow::pure());
        assert_eq!(e.cost_of("memory"), Interval::point(0.0));
        e.set_cost("memory", Interval::range(0.0, 1024.0));
        assert_eq!(e.cost_of("memory"), Interval::range(0.0, 1024.0));
    }

    #[test]
    fn test_row_accessor_reflects_constructed_row() {
        let row = EffectRow::closed(vec![SmolStr::new("State")]);
        let e = Effects::new(row.clone());
        assert_eq!(e.row(), &row);
    }
}
