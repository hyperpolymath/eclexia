// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime support for Eclexia.
//!
//! Provides:
//! - Shadow price tracking for resources
//! - Resource consumption monitoring
//! - Adaptive function decision making
//! - Carbon-aware scheduling integration

mod shadow_prices;
mod resource_tracker;
mod adaptive;

pub use shadow_prices::{ShadowPriceRegistry, ShadowPrice, PriceUpdate};
pub use resource_tracker::{ResourceTracker, ResourceUsage, ResourceBudget};
pub use adaptive::{AdaptiveDecisionEngine, SolutionCandidate, SelectionCriteria};

use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;

/// Runtime configuration
#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    /// Enable shadow price tracking
    pub enable_shadow_prices: bool,

    /// Enable resource usage monitoring
    pub enable_resource_tracking: bool,

    /// Shadow price update interval (milliseconds)
    pub price_update_interval_ms: u64,

    /// Maximum resource budget per function call
    pub max_resource_budget: ResourceBudget,

    /// Enable carbon-aware scheduling
    pub enable_carbon_awareness: bool,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            enable_shadow_prices: true,
            enable_resource_tracking: true,
            price_update_interval_ms: 1000,
            max_resource_budget: ResourceBudget {
                energy: Some(1000.0),    // 1000 J
                time: Some(1.0),          // 1 second
                memory: Some(1024.0),     // 1 KB
                carbon: Some(100.0),      // 100 gCO2e
            },
            enable_carbon_awareness: true,
        }
    }
}

/// Runtime context for eclexia execution
pub struct Runtime {
    /// Configuration
    config: RuntimeConfig,

    /// Shadow price registry
    prices: ShadowPriceRegistry,

    /// Resource tracker
    tracker: ResourceTracker,

    /// Adaptive decision engine
    adaptive: AdaptiveDecisionEngine,
}

impl Runtime {
    /// Create a new runtime with default configuration
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a new runtime with custom configuration
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            config: config.clone(),
            prices: ShadowPriceRegistry::new(),
            tracker: ResourceTracker::new(),
            adaptive: AdaptiveDecisionEngine::new(config),
        }
    }

    /// Get current shadow price for a resource
    pub fn get_shadow_price(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.prices.get_price(resource, dimension)
    }

    /// Update shadow price for a resource
    pub fn update_shadow_price(&mut self, resource: SmolStr, dimension: Dimension, price: f64) {
        self.prices.update_price(resource, dimension, price);
    }

    /// Track resource consumption
    pub fn track_resource(&mut self, resource: SmolStr, dimension: Dimension, amount: f64) {
        if self.config.enable_resource_tracking {
            self.tracker.record_usage(resource, dimension, amount);
        }
    }

    /// Get total resource usage
    pub fn get_resource_usage(&self) -> &[ResourceUsage] {
        self.tracker.get_all_usage()
    }

    /// Select best solution for adaptive function
    pub fn select_solution(&self, candidates: &[SolutionCandidate]) -> Option<usize> {
        self.adaptive.select_best(candidates, &self.prices)
    }

    /// Check if resource budget is exceeded
    pub fn check_budget(&self, usage: &ResourceBudget) -> bool {
        self.tracker.check_budget(usage, &self.config.max_resource_budget)
    }

    /// Reset resource tracking
    pub fn reset_tracking(&mut self) {
        self.tracker.reset();
    }

    /// Get runtime statistics
    pub fn get_stats(&self) -> RuntimeStats {
        RuntimeStats {
            total_resources: self.tracker.get_all_usage().len(),
            total_energy: self.tracker.total_for_dimension(Dimension::energy()),
            total_time: self.tracker.total_for_dimension(Dimension::time()),
            total_memory: self.tracker.total_for_dimension(Dimension::memory()),
            total_carbon: self.tracker.total_for_dimension(Dimension::carbon()),
        }
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}

/// Runtime statistics
#[derive(Debug, Clone)]
pub struct RuntimeStats {
    /// Number of tracked resources
    pub total_resources: usize,

    /// Total energy consumed (Joules)
    pub total_energy: f64,

    /// Total time consumed (seconds)
    pub total_time: f64,

    /// Total memory consumed (bytes)
    pub total_memory: f64,

    /// Total carbon emissions (gCO2e)
    pub total_carbon: f64,
}
