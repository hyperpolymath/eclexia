// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Resource consumption tracking.

use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;

/// Resource usage record
#[derive(Debug, Clone)]
pub struct ResourceUsage {
    /// Resource name
    pub resource: SmolStr,

    /// Resource dimension
    pub dimension: Dimension,

    /// Amount consumed
    pub amount: f64,

    /// Timestamp
    pub timestamp: u64,
}

/// Resource budget limits
#[derive(Debug, Clone)]
pub struct ResourceBudget {
    /// Energy budget (Joules)
    pub energy: Option<f64>,

    /// Time budget (seconds)
    pub time: Option<f64>,

    /// Memory budget (bytes)
    pub memory: Option<f64>,

    /// Carbon budget (gCO2e)
    pub carbon: Option<f64>,
}

impl ResourceBudget {
    /// Create unlimited budget
    pub fn unlimited() -> Self {
        Self {
            energy: None,
            time: None,
            memory: None,
            carbon: None,
        }
    }

    /// Check if any limit is set
    pub fn has_limits(&self) -> bool {
        self.energy.is_some()
            || self.time.is_some()
            || self.memory.is_some()
            || self.carbon.is_some()
    }

    /// Get limit for dimension
    pub fn get_limit(&self, dimension: &Dimension) -> Option<f64> {
        if dimension == &Dimension::energy() {
            self.energy
        } else if dimension == &Dimension::time() {
            self.time
        } else if dimension == &Dimension::memory() {
            self.memory
        } else if dimension == &Dimension::carbon() {
            self.carbon
        } else {
            None
        }
    }
}

/// Resource tracker
pub struct ResourceTracker {
    /// All recorded usage
    usage: Vec<ResourceUsage>,
}

impl ResourceTracker {
    /// Create a new tracker
    pub fn new() -> Self {
        Self { usage: Vec::new() }
    }

    /// Record resource usage
    pub fn record_usage(&mut self, resource: SmolStr, dimension: Dimension, amount: f64) {
        self.usage.push(ResourceUsage {
            resource,
            dimension,
            amount,
            timestamp: current_timestamp(),
        });
    }

    /// Get all usage records
    pub fn get_all_usage(&self) -> &[ResourceUsage] {
        &self.usage
    }

    /// Get total usage for a specific dimension
    pub fn total_for_dimension(&self, dimension: Dimension) -> f64 {
        self.usage
            .iter()
            .filter(|u| u.dimension == dimension)
            .map(|u| u.amount)
            .sum()
    }

    /// Get total usage for a specific resource and dimension
    pub fn total_for_resource(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.usage
            .iter()
            .filter(|u| &u.resource == resource && u.dimension == dimension)
            .map(|u| u.amount)
            .sum()
    }

    /// Check if usage is within budget
    pub fn check_budget(&self, usage: &ResourceBudget, limit: &ResourceBudget) -> bool {
        // Check each dimension
        if let (Some(used), Some(max)) = (usage.energy, limit.energy) {
            if used > max {
                return false;
            }
        }

        if let (Some(used), Some(max)) = (usage.time, limit.time) {
            if used > max {
                return false;
            }
        }

        if let (Some(used), Some(max)) = (usage.memory, limit.memory) {
            if used > max {
                return false;
            }
        }

        if let (Some(used), Some(max)) = (usage.carbon, limit.carbon) {
            if used > max {
                return false;
            }
        }

        true
    }

    /// Reset all tracking
    pub fn reset(&mut self) {
        self.usage.clear();
    }

    /// Get usage summary grouped by resource
    pub fn get_summary(&self) -> Vec<(SmolStr, Dimension, f64)> {
        use rustc_hash::FxHashMap;

        let mut summary: FxHashMap<(SmolStr, Dimension), f64> = FxHashMap::default();

        for usage in &self.usage {
            let key = (usage.resource.clone(), usage.dimension);
            *summary.entry(key).or_insert(0.0) += usage.amount;
        }

        summary
            .into_iter()
            .map(|((resource, dimension), total)| (resource, dimension, total))
            .collect()
    }
}

impl Default for ResourceTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Get current timestamp
fn current_timestamp() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}
