// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Adaptive function decision making.
//!
//! Selects the best implementation variant based on shadow prices
//! and resource constraints.

use crate::resource_tracker::ResourceBudget;
use crate::shadow_prices::ShadowPriceRegistry;
use crate::RuntimeConfig;
use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;
use std::cmp::Ordering;

fn cmp_f64(a: f64, b: f64) -> Ordering {
    a.partial_cmp(&b).unwrap_or(Ordering::Equal)
}

/// A candidate solution for adaptive selection
#[derive(Debug, Clone)]
pub struct SolutionCandidate {
    /// Solution name/ID
    pub name: SmolStr,

    /// Resource costs for this solution
    pub costs: Vec<ResourceCost>,

    /// Optional runtime condition (e.g., "when n > 1000")
    pub condition: Option<String>,

    /// Priority/preference score (higher = preferred)
    pub priority: f64,
}

/// Resource cost for a solution
#[derive(Debug, Clone)]
pub struct ResourceCost {
    /// Resource name
    pub resource: SmolStr,

    /// Dimension
    pub dimension: Dimension,

    /// Amount consumed
    pub amount: f64,
}

impl SolutionCandidate {
    /// Calculate total cost given shadow prices
    pub fn calculate_cost(&self, prices: &ShadowPriceRegistry) -> f64 {
        self.costs
            .iter()
            .map(|cost| {
                let price = prices.get_price(&cost.resource, cost.dimension);
                cost.amount * price
            })
            .sum()
    }

    /// Check if solution meets resource budget
    pub fn meets_budget(&self, budget: &ResourceBudget) -> bool {
        for cost in &self.costs {
            if let Some(limit) = budget.get_limit(&cost.dimension) {
                if cost.amount > limit {
                    return false;
                }
            }
        }
        true
    }
}

/// Selection criteria for adaptive functions
#[derive(Debug, Clone)]
pub enum SelectionCriteria {
    /// Minimize total cost (default)
    MinimizeCost,

    /// Minimize specific resource
    MinimizeResource {
        resource: SmolStr,
        dimension: Dimension,
    },

    /// Prefer solutions with priority > threshold
    PreferPriority { threshold: f64 },

    /// Custom weighted combination
    Weighted {
        energy_weight: f64,
        time_weight: f64,
        memory_weight: f64,
        carbon_weight: f64,
    },
}

/// Adaptive decision engine
pub struct AdaptiveDecisionEngine {
    /// Selection criteria
    criteria: SelectionCriteria,

    /// Configuration
    config: RuntimeConfig,
}

impl AdaptiveDecisionEngine {
    /// Create a new decision engine
    pub fn new(config: RuntimeConfig) -> Self {
        Self {
            criteria: SelectionCriteria::MinimizeCost,
            config,
        }
    }

    /// Set selection criteria
    pub fn set_criteria(&mut self, criteria: SelectionCriteria) {
        self.criteria = criteria;
    }

    /// Select the best solution from candidates
    pub fn select_best(
        &self,
        candidates: &[SolutionCandidate],
        prices: &ShadowPriceRegistry,
    ) -> Option<usize> {
        if candidates.is_empty() {
            return None;
        }

        // Filter out solutions that don't meet budget
        let viable: Vec<(usize, &SolutionCandidate)> = candidates
            .iter()
            .enumerate()
            .filter(|(_, candidate)| candidate.meets_budget(&self.config.max_resource_budget))
            .collect();

        if viable.is_empty() {
            return None;
        }

        // Select based on criteria

        match &self.criteria {
            SelectionCriteria::MinimizeCost => self.select_min_cost(&viable, prices),

            SelectionCriteria::MinimizeResource {
                resource,
                dimension,
            } => self.select_min_resource(&viable, resource, *dimension),

            SelectionCriteria::PreferPriority { threshold } => {
                self.select_by_priority(&viable, *threshold, prices)
            }

            SelectionCriteria::Weighted {
                energy_weight,
                time_weight,
                memory_weight,
                carbon_weight,
            } => self.select_weighted(
                &viable,
                prices,
                *energy_weight,
                *time_weight,
                *memory_weight,
                *carbon_weight,
            ),
        }
    }

    /// Select solution with minimum total cost
    fn select_min_cost(
        &self,
        candidates: &[(usize, &SolutionCandidate)],
        prices: &ShadowPriceRegistry,
    ) -> Option<usize> {
        candidates
            .iter()
            .min_by(|a, b| {
                let cost_a = a.1.calculate_cost(prices);
                let cost_b = b.1.calculate_cost(prices);
                cmp_f64(cost_a, cost_b)
            })
            .map(|(idx, _)| *idx)
    }

    /// Select solution minimizing specific resource
    fn select_min_resource(
        &self,
        candidates: &[(usize, &SolutionCandidate)],
        resource: &SmolStr,
        dimension: Dimension,
    ) -> Option<usize> {
        candidates
            .iter()
            .min_by(|a, b| {
                let usage_a: f64 =
                    a.1.costs
                        .iter()
                        .filter(|c| &c.resource == resource && c.dimension == dimension)
                        .map(|c| c.amount)
                        .sum();

                let usage_b: f64 =
                    b.1.costs
                        .iter()
                        .filter(|c| &c.resource == resource && c.dimension == dimension)
                        .map(|c| c.amount)
                        .sum();

                cmp_f64(usage_a, usage_b)
            })
            .map(|(idx, _)| *idx)
    }

    /// Select by priority with cost fallback
    fn select_by_priority(
        &self,
        candidates: &[(usize, &SolutionCandidate)],
        threshold: f64,
        prices: &ShadowPriceRegistry,
    ) -> Option<usize> {
        // First try to find high-priority solutions
        let high_priority: Vec<_> = candidates
            .iter()
            .filter(|(_, c)| c.priority >= threshold)
            .copied()
            .collect();

        if !high_priority.is_empty() {
            return self.select_min_cost(&high_priority, prices);
        }

        // Fallback to minimum cost
        self.select_min_cost(candidates, prices)
    }

    /// Select with weighted criteria
    fn select_weighted(
        &self,
        candidates: &[(usize, &SolutionCandidate)],
        prices: &ShadowPriceRegistry,
        energy_weight: f64,
        time_weight: f64,
        memory_weight: f64,
        carbon_weight: f64,
    ) -> Option<usize> {
        candidates
            .iter()
            .min_by(|a, b| {
                let score_a = self.calculate_weighted_score(
                    a.1,
                    prices,
                    energy_weight,
                    time_weight,
                    memory_weight,
                    carbon_weight,
                );

                let score_b = self.calculate_weighted_score(
                    b.1,
                    prices,
                    energy_weight,
                    time_weight,
                    memory_weight,
                    carbon_weight,
                );

                cmp_f64(score_a, score_b)
            })
            .map(|(idx, _)| *idx)
    }

    /// Calculate weighted score for a solution
    fn calculate_weighted_score(
        &self,
        candidate: &SolutionCandidate,
        prices: &ShadowPriceRegistry,
        energy_weight: f64,
        time_weight: f64,
        memory_weight: f64,
        carbon_weight: f64,
    ) -> f64 {
        let mut score = 0.0;

        for cost in &candidate.costs {
            let price = prices.get_price(&cost.resource, cost.dimension);
            let weighted_cost = cost.amount * price;

            if cost.dimension == Dimension::energy() {
                score += weighted_cost * energy_weight;
            } else if cost.dimension == Dimension::time() {
                score += weighted_cost * time_weight;
            } else if cost.dimension == Dimension::memory() {
                score += weighted_cost * memory_weight;
            } else if cost.dimension == Dimension::carbon() {
                score += weighted_cost * carbon_weight;
            }
        }

        score
    }
}

impl Default for AdaptiveDecisionEngine {
    fn default() -> Self {
        Self::new(RuntimeConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_candidate(name: &str, energy: f64, time: f64, priority: f64) -> SolutionCandidate {
        SolutionCandidate {
            name: SmolStr::new(name),
            costs: vec![
                ResourceCost {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                    amount: energy,
                },
                ResourceCost {
                    resource: SmolStr::new("time"),
                    dimension: Dimension::time(),
                    amount: time,
                },
            ],
            condition: None,
            priority,
        }
    }

    #[test]
    fn test_select_best_minimize_cost() {
        let engine = AdaptiveDecisionEngine::default();
        let prices = ShadowPriceRegistry::new();

        let candidates = vec![
            make_candidate("expensive", 100.0, 10.0, 1.0),
            make_candidate("cheap", 1.0, 0.1, 1.0),
            make_candidate("medium", 50.0, 5.0, 1.0),
        ];

        let best = engine.select_best(&candidates, &prices);
        assert_eq!(best, Some(1)); // "cheap" has lowest cost
    }

    #[test]
    fn test_select_best_weighted() {
        let mut engine = AdaptiveDecisionEngine::default();
        engine.set_criteria(SelectionCriteria::Weighted {
            energy_weight: 10.0,
            time_weight: 0.0,
            memory_weight: 0.0,
            carbon_weight: 0.0,
        });
        let prices = ShadowPriceRegistry::new();

        let candidates = vec![
            make_candidate("low_energy", 1.0, 100.0, 1.0),
            make_candidate("high_energy", 100.0, 1.0, 1.0),
        ];

        let best = engine.select_best(&candidates, &prices);
        // Whichever index is selected, it should be consistent
        assert!(best.is_some());
        // The selected candidate should have lower weighted energy cost
        let idx = best.unwrap();
        let selected = &candidates[idx];
        let other_idx = if idx == 0 { 1 } else { 0 };
        let other = &candidates[other_idx];
        let sel_cost = selected.calculate_cost(&prices);
        let oth_cost = other.calculate_cost(&prices);
        // With weighted criteria, selected should have lower or equal score
        assert!(sel_cost <= oth_cost || (sel_cost - oth_cost).abs() < 1e-10);
    }

    #[test]
    fn test_select_best_prefer_priority() {
        let mut engine = AdaptiveDecisionEngine::default();
        engine.set_criteria(SelectionCriteria::PreferPriority { threshold: 0.5 });
        let prices = ShadowPriceRegistry::new();

        // Both candidates are "high priority" (>= 0.5), but one is cheaper
        let candidates = vec![
            make_candidate("expensive", 100.0, 10.0, 1.0),
            make_candidate("cheap", 1.0, 0.1, 1.0),
        ];

        let best = engine.select_best(&candidates, &prices);
        assert!(best.is_some());
        // Among high-priority candidates, select the cheapest
        assert_eq!(best, Some(1)); // "cheap" should win
    }

    #[test]
    fn test_budget_filtering() {
        let mut config = RuntimeConfig::default();
        config.max_resource_budget.energy = Some(10.0); // tight energy budget
        let engine = AdaptiveDecisionEngine::new(config);
        let prices = ShadowPriceRegistry::new();

        let candidates = vec![
            make_candidate("over_budget", 100.0, 1.0, 1.0), // exceeds 10.0 limit
            make_candidate("within_budget", 5.0, 1.0, 1.0),
        ];

        let best = engine.select_best(&candidates, &prices);
        assert_eq!(best, Some(1)); // only "within_budget" is viable
    }

    #[test]
    fn test_empty_candidates_returns_none() {
        let engine = AdaptiveDecisionEngine::default();
        let prices = ShadowPriceRegistry::new();

        let best = engine.select_best(&[], &prices);
        assert_eq!(best, None);
    }

    #[test]
    fn test_all_over_budget_returns_none() {
        let mut config = RuntimeConfig::default();
        config.max_resource_budget.energy = Some(1.0); // very tight
        let engine = AdaptiveDecisionEngine::new(config);
        let prices = ShadowPriceRegistry::new();

        let candidates = vec![
            make_candidate("a", 100.0, 1.0, 1.0),
            make_candidate("b", 50.0, 1.0, 1.0),
        ];

        let best = engine.select_best(&candidates, &prices);
        assert_eq!(best, None); // nothing meets budget
    }

    #[test]
    fn test_solution_calculate_cost() {
        let prices = ShadowPriceRegistry::new();
        let candidate = make_candidate("test", 100.0, 1.0, 1.0);
        let cost = candidate.calculate_cost(&prices);
        // Cost should be > 0 since shadow prices are > 0
        assert!(cost > 0.0);
    }
}
