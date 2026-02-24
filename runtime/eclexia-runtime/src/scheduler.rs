// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Adaptive scheduler for solution selection.
//!
//! Selects optimal execution strategies based on current shadow prices,
//! resource budgets, and carbon intensity. Integrates with the adaptive
//! decision engine to schedule work at times/configurations that minimize
//! total economic cost.

use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;
use std::collections::VecDeque;

use crate::carbon::{CarbonMonitor, CarbonSignal};
use crate::resource_tracker::ResourceBudget;
use crate::shadow_prices::ShadowPriceRegistry;

/// A task submitted to the scheduler.
#[derive(Debug, Clone)]
pub struct ScheduledTask {
    /// Unique task identifier.
    pub id: u64,

    /// Human-readable task name.
    pub name: SmolStr,

    /// Estimated resource requirements per resource/dimension.
    pub estimated_costs: Vec<(SmolStr, Dimension, f64)>,

    /// Priority (higher = more urgent, range 0..=100).
    pub priority: u8,

    /// Whether this task can be deferred to a lower-cost window.
    pub deferrable: bool,

    /// Optional carbon intensity signal threshold to wait for.
    pub defer_until: Option<CarbonSignal>,
}

/// Scheduling decision for a task.
#[derive(Debug, Clone, PartialEq)]
pub enum ScheduleDecision {
    /// Execute immediately.
    RunNow,

    /// Defer until resource costs drop below threshold.
    Defer { reason: SmolStr },

    /// Reject — would exceed budget.
    Reject { reason: SmolStr },
}

/// Adaptive scheduler that uses shadow prices to order and gate work.
pub struct Scheduler {
    /// Pending task queue ordered by effective cost.
    queue: VecDeque<ScheduledTask>,

    /// Next task ID.
    next_id: u64,

    /// Cost threshold: if total shadow cost exceeds this, defer deferrable tasks.
    defer_threshold: f64,

    /// Total tasks scheduled (lifetime counter).
    total_scheduled: u64,

    /// Total tasks deferred (lifetime counter).
    total_deferred: u64,

    /// Carbon monitor for defer decisions.
    carbon_monitor: CarbonMonitor,
}

impl Scheduler {
    /// Create a new scheduler.
    pub fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            next_id: 1,
            defer_threshold: 100.0,
            total_scheduled: 0,
            total_deferred: 0,
            carbon_monitor: CarbonMonitor::new(),
        }
    }

    /// Set the cost threshold for deferring tasks.
    pub fn set_defer_threshold(&mut self, threshold: f64) {
        self.defer_threshold = threshold;
    }

    /// Submit a task and get a scheduling decision.
    #[allow(clippy::too_many_arguments)]
    pub fn submit(
        &mut self,
        name: SmolStr,
        estimated_costs: Vec<(SmolStr, Dimension, f64)>,
        priority: u8,
        deferrable: bool,
        defer_until: Option<CarbonSignal>,
        prices: &ShadowPriceRegistry,
        budget: &ResourceBudget,
    ) -> (u64, ScheduleDecision) {
        let id = self.next_id;
        self.next_id += 1;

        let task = ScheduledTask {
            id,
            name,
            estimated_costs,
            priority,
            deferrable,
            defer_until,
        };

        let decision = self.evaluate(&task, prices, budget);

        match &decision {
            ScheduleDecision::RunNow => {
                self.total_scheduled += 1;
            }
            ScheduleDecision::Defer { .. } => {
                self.total_deferred += 1;
                self.queue.push_back(task);
            }
            ScheduleDecision::Reject { .. } => {}
        }

        (id, decision)
    }

    /// Evaluate whether a task should run now, be deferred, or rejected.
    fn evaluate(
        &self,
        task: &ScheduledTask,
        prices: &ShadowPriceRegistry,
        budget: &ResourceBudget,
    ) -> ScheduleDecision {
        // Calculate total shadow cost of the task.
        let total_cost: f64 = task
            .estimated_costs
            .iter()
            .map(|(resource, dim, amount)| {
                let price = prices.get_price(resource, *dim);
                price * amount
            })
            .sum();

        // Check budget limits.
        for (_, dim, amount) in &task.estimated_costs {
            if let Some(limit) = budget.get_limit(dim) {
                if *amount > limit {
                    return ScheduleDecision::Reject {
                        reason: SmolStr::new(format!(
                            "exceeds budget for {:?}: {:.2} > {:.2}",
                            dim, amount, limit
                        )),
                    };
                }
            }
        }

        // High-priority tasks always run.
        if task.priority >= 80 {
            return ScheduleDecision::RunNow;
        }

        // Defer until carbon signal drops below a requested level.
        if let Some(required_signal) = task.defer_until {
            if self.carbon_monitor.signal().level() > required_signal.level() {
                return ScheduleDecision::Defer {
                    reason: SmolStr::new(format!(
                        "waiting for carbon signal {:?} (current: {:?})",
                        required_signal,
                        self.carbon_monitor.signal()
                    )),
                };
            }
        }

        if task.deferrable && self.carbon_monitor.should_defer() {
            return ScheduleDecision::Defer {
                reason: SmolStr::new(format!(
                    "carbon signal {:?} requests deferral",
                    self.carbon_monitor.signal()
                )),
            };
        }

        // Deferrable tasks with high cost get deferred.
        if task.deferrable && total_cost > self.defer_threshold {
            return ScheduleDecision::Defer {
                reason: SmolStr::new(format!(
                    "shadow cost {:.2} exceeds threshold {:.2}",
                    total_cost, self.defer_threshold
                )),
            };
        }

        ScheduleDecision::RunNow
    }

    /// Re-evaluate deferred tasks and return any that should now run.
    pub fn drain_ready(
        &mut self,
        prices: &ShadowPriceRegistry,
        budget: &ResourceBudget,
    ) -> Vec<ScheduledTask> {
        let mut ready = Vec::new();
        let mut still_deferred = VecDeque::new();

        while let Some(task) = self.queue.pop_front() {
            match self.evaluate(&task, prices, budget) {
                ScheduleDecision::RunNow => {
                    self.total_scheduled += 1;
                    ready.push(task);
                }
                ScheduleDecision::Defer { .. } => {
                    still_deferred.push_back(task);
                }
                ScheduleDecision::Reject { .. } => {
                    // Drop rejected tasks silently.
                }
            }
        }

        self.queue = still_deferred;
        ready
    }

    /// Number of tasks currently deferred.
    pub fn deferred_count(&self) -> usize {
        self.queue.len()
    }

    /// Lifetime statistics.
    pub fn stats(&self) -> SchedulerStats {
        SchedulerStats {
            total_scheduled: self.total_scheduled,
            total_deferred: self.total_deferred,
            currently_deferred: self.queue.len() as u64,
        }
    }

    /// Update carbon monitor with a new intensity reading.
    pub fn update_carbon(&mut self, region: SmolStr, intensity: f64) {
        self.carbon_monitor.update_intensity(region, intensity);
    }

    /// Get the current carbon signal.
    pub fn carbon_signal(&self) -> CarbonSignal {
        self.carbon_monitor.signal()
    }
}

impl Default for Scheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// Scheduler statistics.
#[derive(Debug, Clone)]
pub struct SchedulerStats {
    pub total_scheduled: u64,
    pub total_deferred: u64,
    pub currently_deferred: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::carbon::CarbonSignal;

    #[test]
    fn test_high_priority_always_runs() {
        let mut sched = Scheduler::new();
        let prices = ShadowPriceRegistry::new();
        let budget = ResourceBudget::unlimited();

        let (_, decision) = sched.submit(
            SmolStr::new("urgent"),
            vec![(SmolStr::new("energy"), Dimension::energy(), 9999.0)],
            90,
            true,
            None,
            &prices,
            &budget,
        );
        assert_eq!(decision, ScheduleDecision::RunNow);
    }

    #[test]
    fn test_budget_rejection() {
        let mut sched = Scheduler::new();
        let prices = ShadowPriceRegistry::new();
        let budget = ResourceBudget {
            energy: Some(10.0),
            time: None,
            memory: None,
            carbon: None,
        };

        let (_, decision) = sched.submit(
            SmolStr::new("big_task"),
            vec![(SmolStr::new("energy"), Dimension::energy(), 50.0)],
            50,
            false,
            None,
            &prices,
            &budget,
        );
        assert!(matches!(decision, ScheduleDecision::Reject { .. }));
    }

    #[test]
    fn test_deferrable_task_deferred_when_costly() {
        let mut sched = Scheduler::new();
        let mut prices = ShadowPriceRegistry::new();
        // Set a high shadow price to make the task expensive.
        prices.update_price(SmolStr::new("energy"), Dimension::energy(), 200.0);
        sched.set_defer_threshold(50.0);

        let budget = ResourceBudget::unlimited();

        let (_, decision) = sched.submit(
            SmolStr::new("flexible"),
            vec![(SmolStr::new("energy"), Dimension::energy(), 1.0)],
            30,
            true,
            None,
            &prices,
            &budget,
        );
        assert!(matches!(decision, ScheduleDecision::Defer { .. }));
        assert_eq!(sched.deferred_count(), 1);
    }

    #[test]
    fn test_drain_ready_releases_tasks() {
        let mut sched = Scheduler::new();
        let mut prices = ShadowPriceRegistry::new();
        prices.update_price(SmolStr::new("energy"), Dimension::energy(), 200.0);
        sched.set_defer_threshold(50.0);

        let budget = ResourceBudget::unlimited();
        sched.submit(
            SmolStr::new("flex1"),
            vec![(SmolStr::new("energy"), Dimension::energy(), 1.0)],
            30,
            true,
            None,
            &prices,
            &budget,
        );
        assert_eq!(sched.deferred_count(), 1);

        // Drop the price so it's below threshold.
        prices.update_price(SmolStr::new("energy"), Dimension::energy(), 10.0);
        let ready = sched.drain_ready(&prices, &budget);
        assert_eq!(ready.len(), 1);
        assert_eq!(sched.deferred_count(), 0);
    }

    #[test]
    fn test_defer_until_waits_for_green() {
        let mut sched = Scheduler::new();
        let prices = ShadowPriceRegistry::new();
        let budget = ResourceBudget::unlimited();
        sched.update_carbon(SmolStr::new("grid"), 600.0);

        let (_, decision) = sched.submit(
            SmolStr::new("eco"),
            vec![(SmolStr::new("energy"), Dimension::energy(), 1.0)],
            30,
            true,
            Some(CarbonSignal::Green),
            &prices,
            &budget,
        );

        assert!(matches!(decision, ScheduleDecision::Defer { .. }));
    }
}
