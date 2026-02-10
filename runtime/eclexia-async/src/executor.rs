// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Async task executor for Eclexia.
//!
//! Built on tokio's multi-threaded runtime with resource-aware scheduling.
//! Each task carries a resource budget and the executor tracks aggregate
//! resource usage across all tasks.

use parking_lot::RwLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

/// Configuration for the async runtime.
#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    /// Number of worker threads (0 = auto-detect from CPU count).
    pub worker_threads: usize,
    /// Maximum number of concurrent tasks.
    pub max_tasks: usize,
    /// Enable resource tracking across tasks.
    pub enable_resource_tracking: bool,
    /// Enable carbon-aware scheduling (defer tasks during high-carbon periods).
    pub enable_carbon_aware_scheduling: bool,
    /// Global energy budget for all tasks (Joules). None = unlimited.
    pub global_energy_budget: Option<f64>,
    /// Global carbon budget for all tasks (gCO2e). None = unlimited.
    pub global_carbon_budget: Option<f64>,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            worker_threads: 0,
            max_tasks: 10_000,
            enable_resource_tracking: true,
            enable_carbon_aware_scheduling: false,
            global_energy_budget: None,
            global_carbon_budget: None,
        }
    }
}

/// Shared runtime state accessible from all tasks.
#[derive(Debug)]
pub struct RuntimeState {
    /// Total tasks spawned.
    pub tasks_spawned: AtomicU64,
    /// Currently active tasks.
    pub tasks_active: AtomicU64,
    /// Tasks completed successfully.
    pub tasks_completed: AtomicU64,
    /// Tasks that panicked or were cancelled.
    pub tasks_failed: AtomicU64,
    /// Aggregate energy usage across all tasks (Joules * 1000 for precision).
    pub total_energy_mj: AtomicU64,
    /// Aggregate carbon emissions across all tasks (gCO2e * 1000).
    pub total_carbon_ug: AtomicU64,
    /// Whether the runtime is shutting down.
    pub shutting_down: AtomicBool,
}

impl RuntimeState {
    fn new() -> Self {
        Self {
            tasks_spawned: AtomicU64::new(0),
            tasks_active: AtomicU64::new(0),
            tasks_completed: AtomicU64::new(0),
            tasks_failed: AtomicU64::new(0),
            total_energy_mj: AtomicU64::new(0),
            total_carbon_ug: AtomicU64::new(0),
            shutting_down: AtomicBool::new(false),
        }
    }

    /// Record task spawn.
    pub fn on_task_spawn(&self) {
        self.tasks_spawned.fetch_add(1, Ordering::Relaxed);
        self.tasks_active.fetch_add(1, Ordering::Relaxed);
    }

    /// Record task completion.
    pub fn on_task_complete(&self) {
        self.tasks_active.fetch_sub(1, Ordering::Relaxed);
        self.tasks_completed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record task failure.
    pub fn on_task_fail(&self) {
        self.tasks_active.fetch_sub(1, Ordering::Relaxed);
        self.tasks_failed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record energy usage (in millijoules for integer precision).
    pub fn record_energy(&self, millijoules: u64) {
        self.total_energy_mj
            .fetch_add(millijoules, Ordering::Relaxed);
    }

    /// Record carbon emissions (in micrograms CO2e for precision).
    pub fn record_carbon(&self, micrograms: u64) {
        self.total_carbon_ug
            .fetch_add(micrograms, Ordering::Relaxed);
    }
}

/// The Eclexia async runtime.
///
/// Wraps a tokio runtime with resource-aware scheduling and monitoring.
pub struct Runtime {
    /// The underlying tokio runtime.
    inner: tokio::runtime::Runtime,
    /// Shared runtime state.
    state: Arc<RuntimeState>,
    /// Configuration (used for future adaptive scheduling decisions).
    #[allow(dead_code)]
    config: RuntimeConfig,
    /// Shadow prices for resource-aware scheduling.
    shadow_prices: Arc<RwLock<ShadowPrices>>,
}

/// Shadow prices used for resource-aware task scheduling.
#[derive(Debug, Clone)]
pub struct ShadowPrices {
    /// Price of energy (cost per Joule).
    pub energy: f64,
    /// Price of carbon (cost per gCO2e).
    pub carbon: f64,
    /// Price of time (cost per second).
    pub time: f64,
    /// Price of memory (cost per MB).
    pub memory: f64,
}

impl Default for ShadowPrices {
    fn default() -> Self {
        Self {
            energy: 1.0,
            carbon: 1.0,
            time: 1.0,
            memory: 1.0,
        }
    }
}

impl Runtime {
    /// Create a new runtime with the given configuration.
    pub fn new(config: RuntimeConfig) -> Self {
        let mut builder = tokio::runtime::Builder::new_multi_thread();

        if config.worker_threads > 0 {
            builder.worker_threads(config.worker_threads);
        }

        builder.enable_all();

        let inner = builder.build().expect("Failed to create tokio runtime");

        Self {
            inner,
            state: Arc::new(RuntimeState::new()),
            config,
            shadow_prices: Arc::new(RwLock::new(ShadowPrices::default())),
        }
    }

    /// Check if the runtime is running (not shutting down).
    pub fn is_running(&self) -> bool {
        !self.state.shutting_down.load(Ordering::Relaxed)
    }

    /// Run a future to completion on the runtime.
    pub fn block_on<F: std::future::Future>(&self, future: F) -> F::Output {
        self.inner.block_on(future)
    }

    /// Spawn a task on the runtime.
    pub fn spawn<F>(&self, future: F) -> tokio::task::JoinHandle<F::Output>
    where
        F: std::future::Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.state.on_task_spawn();
        let state = Arc::clone(&self.state);

        self.inner.spawn(async move {
            let result = future.await;
            state.on_task_complete();
            result
        })
    }

    /// Get the shared runtime state for monitoring.
    pub fn state(&self) -> &Arc<RuntimeState> {
        &self.state
    }

    /// Get current shadow prices.
    pub fn shadow_prices(&self) -> ShadowPrices {
        self.shadow_prices.read().clone()
    }

    /// Update shadow prices.
    pub fn set_shadow_prices(&self, prices: ShadowPrices) {
        *self.shadow_prices.write() = prices;
    }

    /// Get runtime statistics.
    pub fn stats(&self) -> RuntimeStats {
        RuntimeStats {
            tasks_spawned: self.state.tasks_spawned.load(Ordering::Relaxed),
            tasks_active: self.state.tasks_active.load(Ordering::Relaxed),
            tasks_completed: self.state.tasks_completed.load(Ordering::Relaxed),
            tasks_failed: self.state.tasks_failed.load(Ordering::Relaxed),
            total_energy_j: self.state.total_energy_mj.load(Ordering::Relaxed) as f64 / 1000.0,
            total_carbon_gco2e: self.state.total_carbon_ug.load(Ordering::Relaxed) as f64
                / 1_000_000.0,
        }
    }

    /// Initiate graceful shutdown.
    pub fn shutdown(&self) {
        self.state.shutting_down.store(true, Ordering::Relaxed);
    }
}

/// Runtime statistics snapshot.
#[derive(Debug, Clone)]
pub struct RuntimeStats {
    /// Total tasks ever spawned.
    pub tasks_spawned: u64,
    /// Currently active tasks.
    pub tasks_active: u64,
    /// Successfully completed tasks.
    pub tasks_completed: u64,
    /// Failed/panicked tasks.
    pub tasks_failed: u64,
    /// Total energy consumed (Joules).
    pub total_energy_j: f64,
    /// Total carbon emitted (gCO2e).
    pub total_carbon_gco2e: f64,
}
