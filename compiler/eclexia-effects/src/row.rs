// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Row polymorphism for effect types.
//!
//! Effect rows track the set of effects a function may perform.
//! Row types enable polymorphism over effects — a function can
//! accept any effect row that includes the effects it needs.
//!
//! ## Representation
//!
//! An effect row is an ordered set of effect names:
//! ```text
//! <Console, State<Int> | r>
//! ```
//! where `r` is a row variable (open row) allowing extension.
//!
//! A closed row has no row variable:
//! ```text
//! <Console, State<Int>>
//! ```

use rustc_hash::FxHashSet;
use smol_str::SmolStr;

/// An effect row type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectRow {
    /// A closed row with a fixed set of effects.
    Closed(FxHashSet<SmolStr>),
    /// An open row with known effects plus a row variable.
    Open {
        /// Known effects in the row.
        effects: FxHashSet<SmolStr>,
        /// Row variable name.
        variable: SmolStr,
    },
    /// The empty row (pure function).
    Pure,
}

impl EffectRow {
    /// Create a pure (empty) row.
    pub fn pure() -> Self {
        Self::Pure
    }

    /// Create a closed row from effect names.
    pub fn closed(effects: impl IntoIterator<Item = SmolStr>) -> Self {
        let set: FxHashSet<SmolStr> = effects.into_iter().collect();
        if set.is_empty() {
            Self::Pure
        } else {
            Self::Closed(set)
        }
    }

    /// Create an open row with a row variable.
    pub fn open(effects: impl IntoIterator<Item = SmolStr>, variable: SmolStr) -> Self {
        let set: FxHashSet<SmolStr> = effects.into_iter().collect();
        Self::Open {
            effects: set,
            variable,
        }
    }

    /// Check if the row is pure (no effects).
    pub fn is_pure(&self) -> bool {
        matches!(self, Self::Pure)
    }

    /// Check if the row is open (has a row variable).
    pub fn is_open(&self) -> bool {
        matches!(self, Self::Open { .. })
    }

    /// Check if a specific effect is in the row.
    pub fn contains(&self, effect: &str) -> bool {
        match self {
            Self::Pure => false,
            Self::Closed(effects) => effects.contains(effect),
            Self::Open { effects, .. } => effects.contains(effect),
        }
    }

    /// Get the known effects in the row.
    pub fn effects(&self) -> Vec<SmolStr> {
        match self {
            Self::Pure => vec![],
            Self::Closed(effects) => effects.iter().cloned().collect(),
            Self::Open { effects, .. } => effects.iter().cloned().collect(),
        }
    }

    /// Number of known effects.
    pub fn len(&self) -> usize {
        match self {
            Self::Pure => 0,
            Self::Closed(effects) => effects.len(),
            Self::Open { effects, .. } => effects.len(),
        }
    }

    /// Whether the row has no known effects.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if this row is a subrow of another.
    ///
    /// A subrow relationship means all effects in `self` are present in `other`.
    /// Open rows are always considered subrows of other open rows with the same variable.
    pub fn is_subrow_of(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Pure, _) => true,
            (_, Self::Pure) => self.is_pure(),
            (Self::Closed(a), Self::Closed(b)) => a.is_subset(b),
            (Self::Closed(a), Self::Open { effects: b, .. }) => a.is_subset(b),
            (Self::Open { effects: a, .. }, Self::Open { effects: b, .. }) => a.is_subset(b),
            (Self::Open { .. }, Self::Closed(_)) => false, // open can't be subrow of closed
        }
    }

    /// Compute the row after handling specified effects (row difference).
    ///
    /// Returns the remaining effects after removing handled ones.
    pub fn handle(&self, handled: &[SmolStr]) -> Self {
        match self {
            Self::Pure => Self::Pure,
            Self::Closed(effects) => {
                let remaining: FxHashSet<SmolStr> = effects
                    .iter()
                    .filter(|e| !handled.contains(e))
                    .cloned()
                    .collect();
                if remaining.is_empty() {
                    Self::Pure
                } else {
                    Self::Closed(remaining)
                }
            }
            Self::Open { effects, variable } => {
                let remaining: FxHashSet<SmolStr> = effects
                    .iter()
                    .filter(|e| !handled.contains(e))
                    .cloned()
                    .collect();
                Self::Open {
                    effects: remaining,
                    variable: variable.clone(),
                }
            }
        }
    }

    /// Merge two rows (union of effects).
    pub fn union(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Pure, x) | (x, Self::Pure) => x.clone(),
            (Self::Closed(a), Self::Closed(b)) => Self::Closed(a.union(b).cloned().collect()),
            (
                Self::Open {
                    effects: a,
                    variable,
                },
                Self::Closed(b),
            )
            | (
                Self::Closed(b),
                Self::Open {
                    effects: a,
                    variable,
                },
            ) => Self::Open {
                effects: a.union(b).cloned().collect(),
                variable: variable.clone(),
            },
            (
                Self::Open {
                    effects: a,
                    variable: va,
                },
                Self::Open {
                    effects: b,
                    variable: _vb,
                },
            ) => Self::Open {
                effects: a.union(b).cloned().collect(),
                variable: va.clone(), // prefer first variable
            },
        }
    }
}

impl std::fmt::Display for EffectRow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pure => write!(f, "<>"),
            Self::Closed(effects) => {
                let mut sorted: Vec<_> = effects.iter().collect();
                sorted.sort();
                write!(
                    f,
                    "<{}>",
                    sorted
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Open { effects, variable } => {
                let mut sorted: Vec<_> = effects.iter().collect();
                sorted.sort();
                if sorted.is_empty() {
                    write!(f, "<| {variable}>")
                } else {
                    write!(
                        f,
                        "<{} | {variable}>",
                        sorted
                            .iter()
                            .map(|s| s.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pure_row() {
        let row = EffectRow::pure();
        assert!(row.is_pure());
        assert!(!row.is_open());
        assert!(row.is_empty());
        assert_eq!(row.len(), 0);
    }

    #[test]
    fn test_closed_row() {
        let row = EffectRow::closed(vec![SmolStr::new("Console"), SmolStr::new("State")]);
        assert!(!row.is_pure());
        assert!(!row.is_open());
        assert!(row.contains("Console"));
        assert!(row.contains("State"));
        assert!(!row.contains("IO"));
        assert_eq!(row.len(), 2);
    }

    #[test]
    fn test_closed_empty_is_pure() {
        let row = EffectRow::closed(Vec::<SmolStr>::new());
        assert!(row.is_pure());
    }

    #[test]
    fn test_open_row() {
        let row = EffectRow::open(vec![SmolStr::new("Console")], SmolStr::new("r"));
        assert!(!row.is_pure());
        assert!(row.is_open());
        assert!(row.contains("Console"));
        assert_eq!(row.len(), 1);
    }

    #[test]
    fn test_subrow_pure() {
        let pure = EffectRow::pure();
        let closed = EffectRow::closed(vec![SmolStr::new("Console")]);
        assert!(pure.is_subrow_of(&closed));
        assert!(!closed.is_subrow_of(&pure));
    }

    #[test]
    fn test_subrow_closed() {
        let a = EffectRow::closed(vec![SmolStr::new("Console")]);
        let b = EffectRow::closed(vec![SmolStr::new("Console"), SmolStr::new("State")]);
        assert!(a.is_subrow_of(&b));
        assert!(!b.is_subrow_of(&a));
    }

    #[test]
    fn test_handle_removes_effects() {
        let row = EffectRow::closed(vec![SmolStr::new("Console"), SmolStr::new("State")]);
        let handled = row.handle(&[SmolStr::new("Console")]);
        assert!(!handled.contains("Console"));
        assert!(handled.contains("State"));
        assert_eq!(handled.len(), 1);
    }

    #[test]
    fn test_handle_all_becomes_pure() {
        let row = EffectRow::closed(vec![SmolStr::new("Console")]);
        let handled = row.handle(&[SmolStr::new("Console")]);
        assert!(handled.is_pure());
    }

    #[test]
    fn test_handle_open_stays_open() {
        let row = EffectRow::open(
            vec![SmolStr::new("Console"), SmolStr::new("State")],
            SmolStr::new("r"),
        );
        let handled = row.handle(&[SmolStr::new("Console")]);
        assert!(handled.is_open());
        assert!(!handled.contains("Console"));
        assert_eq!(handled.len(), 1);
    }

    #[test]
    fn test_union() {
        let a = EffectRow::closed(vec![SmolStr::new("Console")]);
        let b = EffectRow::closed(vec![SmolStr::new("State")]);
        let u = a.union(&b);
        assert!(u.contains("Console"));
        assert!(u.contains("State"));
        assert_eq!(u.len(), 2);
    }

    #[test]
    fn test_union_with_pure() {
        let a = EffectRow::closed(vec![SmolStr::new("Console")]);
        let u = a.union(&EffectRow::pure());
        assert_eq!(u.len(), 1);
        assert!(u.contains("Console"));
    }

    #[test]
    fn test_display_pure() {
        assert_eq!(format!("{}", EffectRow::pure()), "<>");
    }

    #[test]
    fn test_display_closed() {
        let row = EffectRow::closed(vec![SmolStr::new("Console")]);
        assert_eq!(format!("{}", row), "<Console>");
    }

    #[test]
    fn test_display_open() {
        let row = EffectRow::open(vec![SmolStr::new("Console")], SmolStr::new("r"));
        assert_eq!(format!("{}", row), "<Console | r>");
    }

    #[test]
    fn test_display_open_empty() {
        let row = EffectRow::open(Vec::<SmolStr>::new(), SmolStr::new("r"));
        assert_eq!(format!("{}", row), "<| r>");
    }
}
