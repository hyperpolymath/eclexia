// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Shadow price tracking and management.
//!
//! Shadow prices represent the marginal cost of consuming one unit of a resource.
//! They guide adaptive function selection to minimize total cost.

use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;
use rustc_hash::FxHashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// A shadow price for a resource
#[derive(Debug, Clone)]
pub struct ShadowPrice {
    /// Resource name
    pub resource: SmolStr,

    /// Resource dimension
    pub dimension: Dimension,

    /// Current price (cost per unit)
    pub price: f64,

    /// Last update timestamp
    pub last_updated: u64,

    /// Price history (for trend analysis)
    pub history: Vec<PriceUpdate>,
}

/// Price update record
#[derive(Debug, Clone)]
pub struct PriceUpdate {
    /// Timestamp
    pub timestamp: u64,

    /// Price value
    pub price: f64,
}

impl ShadowPrice {
    /// Create a new shadow price
    pub fn new(resource: SmolStr, dimension: Dimension, initial_price: f64) -> Self {
        let timestamp = current_timestamp();
        Self {
            resource,
            dimension,
            price: initial_price,
            last_updated: timestamp,
            history: vec![PriceUpdate {
                timestamp,
                price: initial_price,
            }],
        }
    }

    /// Update the price
    pub fn update(&mut self, new_price: f64) {
        self.price = new_price;
        self.last_updated = current_timestamp();
        self.history.push(PriceUpdate {
            timestamp: self.last_updated,
            price: new_price,
        });

        // Keep only last 100 updates
        if self.history.len() > 100 {
            self.history.remove(0);
        }
    }

    /// Get price trend (positive = increasing, negative = decreasing)
    pub fn get_trend(&self) -> f64 {
        if self.history.len() < 2 {
            return 0.0;
        }

        let recent = &self.history[self.history.len() - 10..];
        let first = recent.first().unwrap().price;
        let last = recent.last().unwrap().price;

        (last - first) / first
    }
}

/// Shadow price registry
pub struct ShadowPriceRegistry {
    /// Map from (resource, dimension) to shadow price
    prices: FxHashMap<(SmolStr, Dimension), ShadowPrice>,

    /// Default price for unknown resources
    default_price: f64,
}

impl ShadowPriceRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        let mut registry = Self {
            prices: FxHashMap::default(),
            default_price: 1.0,
        };

        // Initialize with default prices for common resources
        registry.init_defaults();
        registry
    }

    /// Initialize with default prices
    fn init_defaults(&mut self) {
        // Energy: $0.12/kWh ≈ 0.000033 $/J
        self.prices.insert(
            (SmolStr::new("energy"), Dimension::energy()),
            ShadowPrice::new(SmolStr::new("energy"), Dimension::energy(), 0.000033),
        );

        // Time: $0.001/second (arbitrary baseline)
        self.prices.insert(
            (SmolStr::new("time"), Dimension::time()),
            ShadowPrice::new(SmolStr::new("time"), Dimension::time(), 0.001),
        );

        // Memory: $0.0001/MB-second (from cloud pricing)
        self.prices.insert(
            (SmolStr::new("memory"), Dimension::memory()),
            ShadowPrice::new(SmolStr::new("memory"), Dimension::memory(), 0.0000001),
        );

        // Carbon: $50/tCO2e = 0.00005 $/gCO2e (social cost of carbon)
        self.prices.insert(
            (SmolStr::new("carbon"), Dimension::carbon()),
            ShadowPrice::new(SmolStr::new("carbon"), Dimension::carbon(), 0.00005),
        );
    }

    /// Get current price for a resource
    pub fn get_price(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.prices
            .get(&(resource.clone(), dimension))
            .map(|sp| sp.price)
            .unwrap_or(self.default_price)
    }

    /// Update price for a resource
    pub fn update_price(&mut self, resource: SmolStr, dimension: Dimension, price: f64) {
        let key = (resource.clone(), dimension);
        if let Some(sp) = self.prices.get_mut(&key) {
            sp.update(price);
        } else {
            self.prices.insert(
                key,
                ShadowPrice::new(resource, dimension, price),
            );
        }
    }

    /// Get all prices
    pub fn get_all_prices(&self) -> Vec<&ShadowPrice> {
        self.prices.values().collect()
    }

    /// Get price trend for a resource
    pub fn get_trend(&self, resource: &SmolStr, dimension: Dimension) -> f64 {
        self.prices
            .get(&(resource.clone(), dimension))
            .map(|sp| sp.get_trend())
            .unwrap_or(0.0)
    }

    /// Set default price for unknown resources
    pub fn set_default_price(&mut self, price: f64) {
        self.default_price = price;
    }
}

impl Default for ShadowPriceRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Get current timestamp in milliseconds
fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}
