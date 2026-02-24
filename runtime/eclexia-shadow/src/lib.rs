// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Shadow price utilities for Eclexia.
//!
//! Shadow prices represent the marginal cost of consuming one unit of a resource.
//! They guide adaptive selection and scheduling under resource constraints.

use eclexia_ast::dimension::Dimension;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// Price update record.
#[derive(Debug, Clone)]
pub struct PriceUpdate {
    /// Timestamp in milliseconds.
    pub timestamp: u64,

    /// Price value.
    pub price: f64,
}

/// A shadow price for a resource.
#[derive(Debug, Clone)]
pub struct ShadowPrice {
    /// Resource name.
    pub resource: SmolStr,

    /// Resource dimension.
    pub dimension: Dimension,

    /// Current price (cost per unit).
    pub price: f64,

    /// Last update timestamp.
    pub last_updated: u64,

    /// Price history (for trend analysis).
    pub history: Vec<PriceUpdate>,
}

impl ShadowPrice {
    /// Create a new shadow price.
    pub fn new(resource: SmolStr, dimension: Dimension, initial_price: f64) -> Self {
        let timestamp = current_timestamp_ms();
        Self {
            resource,
            dimension,
            price: initial_price.max(0.0),
            last_updated: timestamp,
            history: vec![PriceUpdate {
                timestamp,
                price: initial_price.max(0.0),
            }],
        }
    }

    /// Update the price.
    pub fn update(&mut self, new_price: f64) {
        self.price = new_price.max(0.0);
        self.last_updated = current_timestamp_ms();
        self.history.push(PriceUpdate {
            timestamp: self.last_updated,
            price: self.price,
        });

        // Keep only last 100 updates.
        if self.history.len() > 100 {
            self.history.remove(0);
        }
    }

    /// Get price trend (positive = increasing, negative = decreasing).
    pub fn get_trend(&self) -> f64 {
        if self.history.len() < 2 {
            return 0.0;
        }

        let width = self.history.len().min(10);
        let recent = &self.history[self.history.len() - width..];
        let first = recent.first().map_or(0.0, |entry| entry.price);
        let last = recent.last().map_or(0.0, |entry| entry.price);

        if first.abs() < 1e-12 {
            return last - first;
        }

        (last - first) / first
    }
}

/// Shadow price registry.
pub struct ShadowPriceRegistry {
    /// Map from (resource, dimension) to shadow price.
    prices: FxHashMap<(SmolStr, Dimension), ShadowPrice>,

    /// Default price for unknown resources.
    default_price: f64,
}

impl ShadowPriceRegistry {
    /// Create a new registry with default prices.
    pub fn new() -> Self {
        let mut registry = Self {
            prices: FxHashMap::default(),
            default_price: 1.0,
        };
        registry.init_defaults();
        registry
    }

    fn init_defaults(&mut self) {
        // Energy: $0.12/kWh ~= 0.000033 $/J.
        self.prices.insert(
            (SmolStr::new("energy"), Dimension::energy()),
            ShadowPrice::new(SmolStr::new("energy"), Dimension::energy(), 0.000033),
        );

        // Time baseline.
        self.prices.insert(
            (SmolStr::new("time"), Dimension::time()),
            ShadowPrice::new(SmolStr::new("time"), Dimension::time(), 0.001),
        );

        // Memory baseline.
        self.prices.insert(
            (SmolStr::new("memory"), Dimension::memory()),
            ShadowPrice::new(SmolStr::new("memory"), Dimension::memory(), 0.0000001),
        );

        // Carbon: $50/tCO2e = 0.00005 $/gCO2e.
        self.prices.insert(
            (SmolStr::new("carbon"), Dimension::carbon()),
            ShadowPrice::new(SmolStr::new("carbon"), Dimension::carbon(), 0.00005),
        );
    }

    /// Get current price for a resource.
    pub fn get_price(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.prices
            .get(&(resource.clone(), dimension))
            .map(|entry| entry.price)
            .unwrap_or(self.default_price)
    }

    /// Update price for a resource.
    pub fn update_price(&mut self, resource: SmolStr, dimension: Dimension, price: f64) {
        let key = (resource.clone(), dimension);
        if let Some(existing) = self.prices.get_mut(&key) {
            existing.update(price);
        } else {
            self.prices
                .insert(key, ShadowPrice::new(resource, dimension, price));
        }
    }

    /// Get all registered prices.
    pub fn get_all_prices(&self) -> Vec<&ShadowPrice> {
        self.prices.values().collect()
    }

    /// Number of known prices.
    pub fn len(&self) -> usize {
        self.prices.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.prices.is_empty()
    }

    /// Get price trend for a resource.
    pub fn get_trend(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.prices
            .get(&(resource.clone(), dimension))
            .map(ShadowPrice::get_trend)
            .unwrap_or(0.0)
    }

    /// Set default price for unknown resources.
    pub fn set_default_price(&mut self, price: f64) {
        self.default_price = price.max(0.0);
    }
}

impl Default for ShadowPriceRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// A resource constraint for shadow price computation.
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    /// Constraint name.
    pub name: SmolStr,

    /// Resource dimension this constraint applies to.
    pub dimension: Dimension,

    /// Right-hand side (budget limit).
    pub budget: f64,

    /// Current usage level.
    pub usage: f64,
}

/// Result of shadow price computation.
#[derive(Debug, Clone)]
pub struct ShadowPriceResult {
    /// Computed shadow prices per constraint.
    pub prices: HashMap<SmolStr, f64>,

    /// Whether the computation converged.
    pub converged: bool,

    /// Number of iterations used.
    pub iterations: u32,
}

/// Shadow price computation engine.
pub struct ShadowPriceEngine {
    /// Constraints for the current problem.
    constraints: Vec<ResourceConstraint>,

    /// Maximum iterations for the solver.
    max_iterations: u32,

    /// Convergence tolerance.
    tolerance: f64,

    /// Smoothing factor for exponential moving average (0..1).
    smoothing: f64,

    /// Previous shadow prices for smoothing.
    previous_prices: HashMap<SmolStr, f64>,
}

impl ShadowPriceEngine {
    /// Create a new shadow price engine.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            max_iterations: 100,
            tolerance: 1e-8,
            smoothing: 0.3,
            previous_prices: HashMap::new(),
        }
    }

    /// Set solver parameters.
    pub fn configure(&mut self, max_iterations: u32, tolerance: f64, smoothing: f64) {
        self.max_iterations = max_iterations.max(1);
        self.tolerance = tolerance.max(0.0);
        self.smoothing = smoothing.clamp(0.0, 1.0);
    }

    /// Add a resource constraint.
    pub fn add_constraint(&mut self, constraint: ResourceConstraint) {
        self.constraints.push(constraint);
    }

    /// Clear all constraints.
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
    }

    /// Number of constraints.
    pub fn constraint_count(&self) -> usize {
        self.constraints.len()
    }

    /// Compute shadow prices for the current constraints.
    pub fn compute(&mut self) -> ShadowPriceResult {
        let mut prices: HashMap<SmolStr, f64> = HashMap::new();

        if self.constraints.is_empty() {
            return ShadowPriceResult {
                prices,
                converged: true,
                iterations: 0,
            };
        }

        for constraint in &self.constraints {
            if constraint.budget <= self.tolerance {
                prices.insert(constraint.name.clone(), 1e6);
                continue;
            }

            let utilization = (constraint.usage / constraint.budget).max(0.0);
            let raw_price = if utilization <= 0.5 {
                utilization * 0.1
            } else if utilization <= 0.8 {
                0.05 + (utilization - 0.5) * 1.0
            } else if utilization <= 1.0 {
                0.35 + (utilization - 0.8) * 5.0
            } else {
                1.35 + (utilization - 1.0) * 10.0
            };

            prices.insert(constraint.name.clone(), raw_price.max(0.0));
        }

        // Apply exponential moving average smoothing.
        for (name, price) in &mut prices {
            if let Some(previous) = self.previous_prices.get(name) {
                *price = self.smoothing * *price + (1.0 - self.smoothing) * *previous;
            }
            *price = (*price).max(0.0);
        }

        self.previous_prices = prices.clone();

        ShadowPriceResult {
            prices,
            converged: true,
            iterations: 1,
        }
    }

    /// Compute and return prices as dimension-keyed values.
    pub fn compute_for_dimensions(&mut self) -> Vec<(SmolStr, Dimension, f64)> {
        let result = self.compute();
        let mut out = Vec::new();

        for constraint in &self.constraints {
            if let Some(price) = result.prices.get(&constraint.name) {
                out.push((constraint.name.clone(), constraint.dimension, *price));
            }
        }

        out
    }
}

impl Default for ShadowPriceEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute weighted cost from resource amounts and current shadow prices.
pub fn compute_weighted_cost(
    costs: &[(SmolStr, Dimension, f64)],
    prices: &ShadowPriceRegistry,
) -> f64 {
    costs
        .iter()
        .map(|(resource, dimension, amount)| prices.get_price(resource, *dimension) * *amount)
        .sum()
}

fn current_timestamp_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_defaults() {
        let registry = ShadowPriceRegistry::new();
        assert!(registry.get_price(&SmolStr::new("energy"), Dimension::energy()) > 0.0);
        assert!(registry.get_price(&SmolStr::new("carbon"), Dimension::carbon()) > 0.0);
    }

    #[test]
    fn test_unknown_price_uses_default() {
        let mut registry = ShadowPriceRegistry::new();
        registry.set_default_price(42.0);
        let price = registry.get_price(&SmolStr::new("unknown"), Dimension::power());
        assert_eq!(price, 42.0);
    }

    #[test]
    fn test_trend_handles_zero_baseline() {
        let mut p = ShadowPrice::new(SmolStr::new("x"), Dimension::energy(), 0.0);
        p.update(2.0);
        let trend = p.get_trend();
        assert!(trend >= 0.0);
    }

    #[test]
    fn test_empty_constraints() {
        let mut engine = ShadowPriceEngine::new();
        let result = engine.compute();
        assert!(result.converged);
        assert!(result.prices.is_empty());
    }

    #[test]
    fn test_slack_constraint_low_price() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            budget: 1000.0,
            usage: 100.0,
        });

        let result = engine.compute();
        let price = result.prices["energy"];
        assert!(price < 0.1);
    }

    #[test]
    fn test_tight_constraint_high_price() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("time"),
            dimension: Dimension::time(),
            budget: 1.0,
            usage: 0.95,
        });

        let result = engine.compute();
        let price = result.prices["time"];
        assert!(price > 0.5);
    }

    #[test]
    fn test_over_budget_penalty() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("memory"),
            dimension: Dimension::memory(),
            budget: 1024.0,
            usage: 2048.0,
        });

        let result = engine.compute();
        let price = result.prices["memory"];
        assert!(price > 1.0);
    }

    #[test]
    fn test_zero_budget_infeasible() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("zero"),
            dimension: Dimension::carbon(),
            budget: 0.0,
            usage: 1.0,
        });

        let result = engine.compute();
        let price = result.prices["zero"];
        assert!(price > 1000.0);
    }

    #[test]
    fn test_non_negative_prices_across_range() {
        for budget in [1.0, 10.0, 100.0] {
            for usage in [0.0, 1.0, 5.0, 50.0, 200.0] {
                let mut engine = ShadowPriceEngine::new();
                engine.add_constraint(ResourceConstraint {
                    name: SmolStr::new("r"),
                    dimension: Dimension::energy(),
                    budget,
                    usage,
                });
                let result = engine.compute();
                assert!(result.prices["r"] >= 0.0);
            }
        }
    }

    #[test]
    fn test_smoothing() {
        let mut engine = ShadowPriceEngine::new();
        engine.configure(100, 1e-8, 0.5);

        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("cpu"),
            dimension: Dimension::time(),
            budget: 1.0,
            usage: 0.9,
        });
        let r1 = engine.compute();
        let p1 = r1.prices["cpu"];

        engine.clear_constraints();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("cpu"),
            dimension: Dimension::time(),
            budget: 1.0,
            usage: 0.1,
        });
        let r2 = engine.compute();
        let p2 = r2.prices["cpu"];

        assert!(p2 > 0.0);
        assert!(p2 < p1);
    }

    #[test]
    fn test_multiple_constraints() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("energy"),
            dimension: Dimension::energy(),
            budget: 100.0,
            usage: 90.0,
        });
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("carbon"),
            dimension: Dimension::carbon(),
            budget: 50.0,
            usage: 10.0,
        });

        let result = engine.compute();
        assert_eq!(result.prices.len(), 2);
        assert!(result.prices["energy"] > result.prices["carbon"]);
    }

    #[test]
    fn test_dimension_output() {
        let mut engine = ShadowPriceEngine::new();
        engine.add_constraint(ResourceConstraint {
            name: SmolStr::new("e"),
            dimension: Dimension::energy(),
            budget: 100.0,
            usage: 50.0,
        });

        let dim_prices = engine.compute_for_dimensions();
        assert_eq!(dim_prices.len(), 1);
        assert_eq!(dim_prices[0].0.as_str(), "e");
    }

    #[test]
    fn test_compute_weighted_cost() {
        let registry = ShadowPriceRegistry::new();
        let costs = vec![
            (SmolStr::new("energy"), Dimension::energy(), 10.0),
            (SmolStr::new("carbon"), Dimension::carbon(), 5.0),
        ];

        let total = compute_weighted_cost(&costs, &registry);
        assert!(total > 0.0);
    }
}
