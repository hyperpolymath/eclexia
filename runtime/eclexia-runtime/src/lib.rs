// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime support for Eclexia.
//!
//! Provides:
//! - Shadow price tracking for resources
//! - Resource consumption monitoring
//! - Adaptive function decision making
//! - Carbon-aware scheduling integration

mod adaptive;
mod carbon;
mod health;
mod power_metrics;
mod profiler;
mod resource_tracker;
mod scheduler;
mod shadow;
mod shadow_prices;

pub use adaptive::{AdaptiveDecisionEngine, SelectionCriteria, SolutionCandidate};
pub use carbon::{
    CarbonError, CarbonForecast, CarbonMonitor, CarbonProvider, CarbonReading, CarbonSignal,
    LocalHeuristicProvider, StaticCarbonProvider,
};
use eclexia_ast::dimension::Dimension;
pub use health::HealthServer;
pub use power_metrics::{PowerMetrics, PowerSample};
pub use profiler::{ProfileSpan, Profiler};
pub use resource_tracker::{ResourceBudget, ResourceTracker, ResourceUsage};
pub use scheduler::{ScheduleDecision, ScheduledTask, Scheduler, SchedulerStats};
pub use shadow::{ResourceConstraint, ShadowPriceEngine, ShadowPriceResult};
pub use shadow_prices::{PriceUpdate, ShadowPrice, ShadowPriceRegistry};
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
                energy: Some(1000.0), // 1000 J
                time: Some(1.0),      // 1 second
                memory: Some(1024.0), // 1 KB
                carbon: Some(100.0),  // 100 gCO2e
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

    /// Carbon monitor for scheduling signals
    carbon_monitor: CarbonMonitor,

    /// Scheduler for adaptive work
    scheduler: Scheduler,

    /// Power metrics sampler
    power_metrics: PowerMetrics,
}

impl Runtime {
    /// Create a new runtime with default configuration
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a new runtime with custom configuration
    pub fn with_config(config: RuntimeConfig) -> Self {
        let cfg = config.clone();

        Self {
            config: cfg.clone(),
            prices: ShadowPriceRegistry::new(),
            tracker: ResourceTracker::new(),
            adaptive: AdaptiveDecisionEngine::new(cfg),
            carbon_monitor: CarbonMonitor::new(),
            scheduler: Scheduler::new(),
            power_metrics: PowerMetrics::new(),
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

    /// Ingest resource samples from another system (e.g., the VM) and record them
    pub fn ingest_usage<I>(&mut self, usage: I)
    where
        I: IntoIterator<Item = (SmolStr, Dimension, f64)>,
    {
        for (resource, dimension, amount) in usage {
            self.track_resource(resource, dimension, amount);
        }
    }

    /// Refresh the shadow price registry based on the tracked resource usage.
    ///
    /// Returns the list of (resource, dimension, price) tuples that were computed.
    pub fn refresh_shadow_prices_from_usage(&mut self) -> Vec<(SmolStr, Dimension, f64)> {
        if !self.config.enable_shadow_prices {
            return Vec::new();
        }

        let summary = self.tracker.get_summary();
        if summary.is_empty() {
            return Vec::new();
        }

        let mut engine = ShadowPriceEngine::new();

        for (resource, dimension, usage) in &summary {
            let budget = self
                .config
                .max_resource_budget
                .get_limit(dimension)
                .unwrap_or(usage.max(1.0));

            if budget <= 0.0 {
                continue;
            }

            engine.add_constraint(ResourceConstraint {
                name: resource.clone(),
                dimension: *dimension,
                budget,
                usage: *usage,
            });
        }

        if engine.constraint_count() == 0 {
            return Vec::new();
        }

        let computed = engine.compute_for_dimensions();

        for (resource, dimension, price) in &computed {
            self.prices
                .update_price(resource.clone(), *dimension, *price);
        }

        computed
    }

    /// Select best solution for adaptive function
    pub fn select_solution(&self, candidates: &[SolutionCandidate]) -> Option<usize> {
        self.adaptive.select_best(candidates, &self.prices)
    }

    /// Check if resource budget is exceeded
    pub fn check_budget(&self, usage: &ResourceBudget) -> bool {
        self.tracker
            .check_budget(usage, &self.config.max_resource_budget)
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

    /// Update carbon intensity readings.
    pub fn update_carbon_reading(&mut self, region: SmolStr, intensity: f64) {
        self.carbon_monitor
            .update_intensity(region.clone(), intensity);
        self.scheduler.update_carbon(region, intensity);
    }

    /// Schedule a task using the adaptive scheduler.
    pub fn schedule_task(
        &mut self,
        name: SmolStr,
        estimated_costs: Vec<(SmolStr, Dimension, f64)>,
        priority: u8,
        deferrable: bool,
        defer_until: Option<CarbonSignal>,
    ) -> (u64, ScheduleDecision) {
        self.scheduler.submit(
            name,
            estimated_costs,
            priority,
            deferrable,
            defer_until,
            &self.prices,
            &self.config.max_resource_budget,
        )
    }

    /// Capture real system metrics (energy/time/carbon) if available.
    pub fn capture_system_metrics(&mut self) -> Option<PowerSample> {
        if let Some(sample) = self.power_metrics.sample() {
            self.track_resource(
                SmolStr::new("energy"),
                Dimension::energy(),
                sample.energy_joules,
            );
            self.track_resource(
                SmolStr::new("time"),
                Dimension::time(),
                sample.duration_secs,
            );
            self.track_resource(
                SmolStr::new("carbon"),
                Dimension::carbon(),
                sample.carbon_gco2e,
            );
            Some(sample)
        } else {
            None
        }
    }

    /// Snapshot of runtime health.
    pub fn health_snapshot(&self) -> RuntimeHealth {
        RuntimeHealth {
            stats: self.get_stats(),
            scheduler: self.scheduler.stats(),
            carbon_signal: self.scheduler.carbon_signal(),
        }
    }

    /// Whether the runtime is ready (not exceeding configured budgets).
    pub fn is_ready(&self) -> bool {
        let stats = self.get_stats();
        let energy_ok = self
            .config
            .max_resource_budget
            .energy
            .map_or(true, |limit| stats.total_energy <= limit);
        let carbon_ok = self
            .config
            .max_resource_budget
            .carbon
            .map_or(true, |limit| stats.total_carbon <= limit);
        energy_ok && carbon_ok
    }

    /// Scheduler statistics for reporting.
    pub fn scheduler_stats(&self) -> SchedulerStats {
        self.scheduler.stats()
    }

    /// Current carbon signal level.
    pub fn carbon_signal(&self) -> CarbonSignal {
        self.scheduler.carbon_signal()
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

/// Snapshot of overall runtime health.
#[derive(Debug, Clone)]
pub struct RuntimeHealth {
    /// Runtime resource statistics
    pub stats: RuntimeStats,

    /// Scheduler metrics
    pub scheduler: SchedulerStats,

    /// Current carbon intensity signal
    pub carbon_signal: CarbonSignal,
}
