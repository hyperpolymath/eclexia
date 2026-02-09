// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Tiered execution management.
//!
//! Tracks function "hotness" and decides when to promote
//! functions from lower tiers (interpreted) to higher tiers
//! (native compiled).

use rustc_hash::FxHashMap;
use smol_str::SmolStr;

/// Execution tier for a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Tier {
    /// Tier 0: Tree-walking interpreter (instant startup).
    Interpreter = 0,
    /// Tier 1: Bytecode VM (fast compilation).
    Bytecode = 1,
    /// Tier 2: Cranelift native (moderate compile, good speed).
    Cranelift = 2,
    /// Tier 3: LLVM native with PGO (slow compile, max speed).
    Llvm = 3,
}

impl Tier {
    /// Get the next tier (if any).
    pub fn next(self) -> Option<Self> {
        match self {
            Self::Interpreter => Some(Self::Bytecode),
            Self::Bytecode => Some(Self::Cranelift),
            Self::Cranelift => Some(Self::Llvm),
            Self::Llvm => None,
        }
    }

    /// Get the tier name.
    pub fn name(self) -> &'static str {
        match self {
            Self::Interpreter => "interpreter",
            Self::Bytecode => "bytecode",
            Self::Cranelift => "cranelift",
            Self::Llvm => "llvm",
        }
    }
}

impl std::fmt::Display for Tier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tier {} ({})", *self as u8, self.name())
    }
}

/// Configuration for tier promotion thresholds.
#[derive(Debug, Clone)]
pub struct TierConfig {
    /// Call count to promote from Tier 0 → Tier 1.
    pub interpreter_to_bytecode: u64,
    /// Call count to promote from Tier 1 → Tier 2.
    pub bytecode_to_cranelift: u64,
    /// Call count to promote from Tier 2 → Tier 3.
    pub cranelift_to_llvm: u64,
}

impl Default for TierConfig {
    fn default() -> Self {
        Self {
            interpreter_to_bytecode: 10,
            bytecode_to_cranelift: 1_000,
            cranelift_to_llvm: 50_000,
        }
    }
}

/// Per-function hotness tracking.
#[derive(Debug, Clone)]
struct FunctionHotness {
    /// Current execution tier.
    tier: Tier,
    /// Total call count.
    call_count: u64,
}

/// Tiered execution manager.
///
/// Tracks function call counts and recommends tier promotions.
#[derive(Debug, Clone)]
pub struct TierManager {
    config: TierConfig,
    functions: FxHashMap<SmolStr, FunctionHotness>,
}

impl TierManager {
    /// Create a new tier manager with default config.
    pub fn new() -> Self {
        Self::with_config(TierConfig::default())
    }

    /// Create a tier manager with custom config.
    pub fn with_config(config: TierConfig) -> Self {
        Self {
            config,
            functions: FxHashMap::default(),
        }
    }

    /// Record a function call and check for tier promotion.
    ///
    /// Returns `Some(new_tier)` if the function should be promoted.
    pub fn record_call(&mut self, function: &SmolStr) -> Option<Tier> {
        let entry = self.functions.entry(function.clone()).or_insert(FunctionHotness {
            tier: Tier::Interpreter,
            call_count: 0,
        });

        entry.call_count += 1;

        let threshold = match entry.tier {
            Tier::Interpreter => self.config.interpreter_to_bytecode,
            Tier::Bytecode => self.config.bytecode_to_cranelift,
            Tier::Cranelift => self.config.cranelift_to_llvm,
            Tier::Llvm => return None,
        };

        if entry.call_count >= threshold {
            if let Some(next) = entry.tier.next() {
                entry.tier = next;
                entry.call_count = 0;
                return Some(next);
            }
        }

        None
    }

    /// Get the current tier of a function.
    pub fn get_tier(&self, function: &str) -> Tier {
        self.functions
            .get(function)
            .map(|h| h.tier)
            .unwrap_or(Tier::Interpreter)
    }

    /// Get the call count of a function.
    pub fn get_call_count(&self, function: &str) -> u64 {
        self.functions
            .get(function)
            .map(|h| h.call_count)
            .unwrap_or(0)
    }

    /// Get all functions at a given tier.
    pub fn functions_at_tier(&self, tier: Tier) -> Vec<SmolStr> {
        self.functions
            .iter()
            .filter(|(_, h)| h.tier == tier)
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// Number of tracked functions.
    pub fn tracked_count(&self) -> usize {
        self.functions.len()
    }
}

impl Default for TierManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tier_ordering() {
        assert!(Tier::Interpreter < Tier::Bytecode);
        assert!(Tier::Bytecode < Tier::Cranelift);
        assert!(Tier::Cranelift < Tier::Llvm);
    }

    #[test]
    fn test_tier_next() {
        assert_eq!(Tier::Interpreter.next(), Some(Tier::Bytecode));
        assert_eq!(Tier::Bytecode.next(), Some(Tier::Cranelift));
        assert_eq!(Tier::Cranelift.next(), Some(Tier::Llvm));
        assert_eq!(Tier::Llvm.next(), None);
    }

    #[test]
    fn test_tier_display() {
        assert_eq!(format!("{}", Tier::Interpreter), "Tier 0 (interpreter)");
        assert_eq!(format!("{}", Tier::Llvm), "Tier 3 (llvm)");
    }

    #[test]
    fn test_tier_manager_initial() {
        let mgr = TierManager::new();
        assert_eq!(mgr.get_tier("unknown"), Tier::Interpreter);
        assert_eq!(mgr.get_call_count("unknown"), 0);
    }

    #[test]
    fn test_tier_promotion_interpreter_to_bytecode() {
        let config = TierConfig {
            interpreter_to_bytecode: 5,
            bytecode_to_cranelift: 100,
            cranelift_to_llvm: 1000,
        };
        let mut mgr = TierManager::with_config(config);
        let func = SmolStr::new("hot_fn");

        // Calls 1-4: no promotion
        for _ in 0..4 {
            assert!(mgr.record_call(&func).is_none());
        }

        // Call 5: promote to Bytecode
        assert_eq!(mgr.record_call(&func), Some(Tier::Bytecode));
        assert_eq!(mgr.get_tier("hot_fn"), Tier::Bytecode);
        assert_eq!(mgr.get_call_count("hot_fn"), 0); // reset after promotion
    }

    #[test]
    fn test_tier_promotion_through_all_tiers() {
        let config = TierConfig {
            interpreter_to_bytecode: 2,
            bytecode_to_cranelift: 3,
            cranelift_to_llvm: 4,
        };
        let mut mgr = TierManager::with_config(config);
        let func = SmolStr::new("very_hot");

        // Interpreter → Bytecode (at call 2)
        mgr.record_call(&func);
        assert_eq!(mgr.record_call(&func), Some(Tier::Bytecode));

        // Bytecode → Cranelift (at call 3)
        mgr.record_call(&func);
        mgr.record_call(&func);
        assert_eq!(mgr.record_call(&func), Some(Tier::Cranelift));

        // Cranelift → LLVM (at call 4)
        mgr.record_call(&func);
        mgr.record_call(&func);
        mgr.record_call(&func);
        assert_eq!(mgr.record_call(&func), Some(Tier::Llvm));

        // No further promotion
        for _ in 0..100 {
            assert!(mgr.record_call(&func).is_none());
        }
    }

    #[test]
    fn test_functions_at_tier() {
        let config = TierConfig {
            interpreter_to_bytecode: 1,
            bytecode_to_cranelift: 100,
            cranelift_to_llvm: 1000,
        };
        let mut mgr = TierManager::with_config(config);

        let f1 = SmolStr::new("cold");
        let f2 = SmolStr::new("hot");

        mgr.record_call(&f1); // promoted to bytecode
        mgr.record_call(&f2); // promoted to bytecode

        // Record one more for f1 (stays at bytecode since threshold is 100)
        mgr.record_call(&f1);

        let bytecode_fns = mgr.functions_at_tier(Tier::Bytecode);
        assert_eq!(bytecode_fns.len(), 2);
    }

    #[test]
    fn test_tracked_count() {
        let mut mgr = TierManager::new();
        assert_eq!(mgr.tracked_count(), 0);

        mgr.record_call(&SmolStr::new("a"));
        mgr.record_call(&SmolStr::new("b"));
        mgr.record_call(&SmolStr::new("a"));

        assert_eq!(mgr.tracked_count(), 2);
    }
}
