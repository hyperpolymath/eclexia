// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Profile data collection and serialization for PGO.
//!
//! Instrumented bytecode collects runtime statistics that
//! feed back into the compiler for profile-guided optimization.

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// Profile data collected from instrumented execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileData {
    /// Per-function profile data.
    pub functions: FxHashMap<String, FunctionProfile>,
    /// Total execution time in microseconds.
    pub total_execution_us: u64,
}

/// Profile data for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionProfile {
    /// Total call count.
    pub call_count: u64,
    /// Total execution time in microseconds.
    pub total_time_us: u64,
    /// Branch frequencies: (block_id, taken_count, not_taken_count).
    pub branch_frequencies: Vec<BranchProfile>,
    /// Resource usage samples.
    pub resource_samples: Vec<ResourceSample>,
}

/// Branch frequency data for a conditional.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BranchProfile {
    /// Block index containing the branch.
    pub block_index: usize,
    /// Times the true branch was taken.
    pub taken: u64,
    /// Times the false branch was taken.
    pub not_taken: u64,
}

impl BranchProfile {
    /// Probability of taking the true branch.
    pub fn taken_probability(&self) -> f64 {
        let total = self.taken + self.not_taken;
        if total == 0 {
            0.5
        } else {
            self.taken as f64 / total as f64
        }
    }

    /// Whether this is a hot branch (called often).
    pub fn is_hot(&self, threshold: u64) -> bool {
        self.taken + self.not_taken >= threshold
    }
}

/// A resource usage sample from one execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceSample {
    /// Resource name.
    pub resource: String,
    /// Measured usage.
    pub amount: f64,
}

impl ProfileData {
    /// Create empty profile data.
    pub fn new() -> Self {
        Self {
            functions: FxHashMap::default(),
            total_execution_us: 0,
        }
    }

    /// Record a function call.
    pub fn record_call(&mut self, function: &str, duration_us: u64) {
        let entry = self
            .functions
            .entry(function.to_string())
            .or_insert_with(|| FunctionProfile {
                call_count: 0,
                total_time_us: 0,
                branch_frequencies: vec![],
                resource_samples: vec![],
            });
        entry.call_count += 1;
        entry.total_time_us += duration_us;
        self.total_execution_us += duration_us;
    }

    /// Record a branch decision.
    pub fn record_branch(&mut self, function: &str, block_index: usize, taken: bool) {
        let entry = self
            .functions
            .entry(function.to_string())
            .or_insert_with(|| FunctionProfile {
                call_count: 0,
                total_time_us: 0,
                branch_frequencies: vec![],
                resource_samples: vec![],
            });

        if let Some(branch) = entry
            .branch_frequencies
            .iter_mut()
            .find(|b| b.block_index == block_index)
        {
            if taken {
                branch.taken += 1;
            } else {
                branch.not_taken += 1;
            }
        } else {
            entry.branch_frequencies.push(BranchProfile {
                block_index,
                taken: if taken { 1 } else { 0 },
                not_taken: if taken { 0 } else { 1 },
            });
        }
    }

    /// Record a resource usage sample.
    pub fn record_resource(&mut self, function: &str, resource: &str, amount: f64) {
        let entry = self
            .functions
            .entry(function.to_string())
            .or_insert_with(|| FunctionProfile {
                call_count: 0,
                total_time_us: 0,
                branch_frequencies: vec![],
                resource_samples: vec![],
            });

        entry.resource_samples.push(ResourceSample {
            resource: resource.to_string(),
            amount,
        });
    }

    /// Get the hottest functions (sorted by call count, descending).
    pub fn hottest_functions(&self, limit: usize) -> Vec<(&str, u64)> {
        let mut funcs: Vec<_> = self
            .functions
            .iter()
            .map(|(name, profile)| (name.as_str(), profile.call_count))
            .collect();
        funcs.sort_by(|a, b| b.1.cmp(&a.1));
        funcs.truncate(limit);
        funcs
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Number of profiled functions.
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
}

impl Default for ProfileData {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(err) => panic!("Expected Ok, got Err: {:?}", err),
        }
    }

    #[test]
    fn test_profile_data_new() {
        let pd = ProfileData::new();
        assert_eq!(pd.function_count(), 0);
        assert_eq!(pd.total_execution_us, 0);
    }

    #[test]
    fn test_record_call() {
        let mut pd = ProfileData::new();
        pd.record_call("main", 100);
        pd.record_call("main", 200);
        pd.record_call("helper", 50);

        assert_eq!(pd.function_count(), 2);
        assert_eq!(pd.functions["main"].call_count, 2);
        assert_eq!(pd.functions["main"].total_time_us, 300);
        assert_eq!(pd.total_execution_us, 350);
    }

    #[test]
    fn test_record_branch() {
        let mut pd = ProfileData::new();
        pd.record_branch("main", 3, true);
        pd.record_branch("main", 3, true);
        pd.record_branch("main", 3, false);

        let branch = &pd.functions["main"].branch_frequencies[0];
        assert_eq!(branch.block_index, 3);
        assert_eq!(branch.taken, 2);
        assert_eq!(branch.not_taken, 1);
        assert!((branch.taken_probability() - 0.666).abs() < 0.01);
    }

    #[test]
    fn test_record_resource() {
        let mut pd = ProfileData::new();
        pd.record_resource("main", "energy", 42.0);
        pd.record_resource("main", "memory", 1024.0);

        assert_eq!(pd.functions["main"].resource_samples.len(), 2);
        assert_eq!(pd.functions["main"].resource_samples[0].resource, "energy");
        assert_eq!(pd.functions["main"].resource_samples[0].amount, 42.0);
    }

    #[test]
    fn test_hottest_functions() {
        let mut pd = ProfileData::new();
        for _ in 0..100 {
            pd.record_call("hot", 10);
        }
        for _ in 0..10 {
            pd.record_call("warm", 10);
        }
        pd.record_call("cold", 10);

        let hot = pd.hottest_functions(2);
        assert_eq!(hot.len(), 2);
        assert_eq!(hot[0].0, "hot");
        assert_eq!(hot[0].1, 100);
        assert_eq!(hot[1].0, "warm");
    }

    #[test]
    fn test_json_roundtrip() {
        let mut pd = ProfileData::new();
        pd.record_call("main", 100);
        pd.record_branch("main", 0, true);
        pd.record_resource("main", "energy", 50.0);

        let json = expect_ok(pd.to_json());
        let pd2 = expect_ok(ProfileData::from_json(&json));

        assert_eq!(pd2.function_count(), 1);
        assert_eq!(pd2.functions["main"].call_count, 1);
        assert_eq!(pd2.functions["main"].branch_frequencies[0].taken, 1);
    }

    #[test]
    fn test_branch_probability_zero() {
        let branch = BranchProfile {
            block_index: 0,
            taken: 0,
            not_taken: 0,
        };
        assert_eq!(branch.taken_probability(), 0.5);
    }

    #[test]
    fn test_branch_is_hot() {
        let branch = BranchProfile {
            block_index: 0,
            taken: 50,
            not_taken: 60,
        };
        assert!(branch.is_hot(100));
        assert!(!branch.is_hot(200));
    }
}
