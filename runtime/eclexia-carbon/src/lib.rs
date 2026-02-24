// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Carbon APIs and green metrics for Eclexia.
//!
//! This crate provides:
//! - Carbon intensity monitoring and signal classification
//! - Carbon emission estimation from energy usage
//! - Provider abstraction for real-time and forecasted grid data
//! - Local fallback heuristics for offline operation

use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::error::Error;
use std::fmt;
use std::time::{SystemTime, UNIX_EPOCH};

/// Carbon intensity reading.
#[derive(Debug, Clone)]
pub struct CarbonReading {
    /// Grid region identifier.
    pub region: SmolStr,

    /// Carbon intensity in gCO2e per kWh.
    pub intensity_gco2e_per_kwh: f64,

    /// Timestamp when this reading was taken (unix seconds).
    pub timestamp: u64,
}

/// Forecasted carbon intensity point.
#[derive(Debug, Clone, PartialEq)]
pub struct CarbonForecast {
    /// Timestamp for the forecast point (unix seconds).
    pub timestamp: u64,

    /// Carbon intensity in gCO2e per kWh.
    pub intensity_gco2e_per_kwh: f64,

    /// Confidence score in [0.0, 1.0].
    pub confidence: f64,
}

/// Scheduling signal based on carbon intensity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CarbonSignal {
    /// Intensity is low, best time to run work.
    Green,

    /// Intensity is moderate, run if needed.
    Yellow,

    /// Intensity is high, defer non-essential work.
    Red,
}

impl CarbonSignal {
    /// Numeric level (Green=0, Yellow=1, Red=2).
    pub fn level(&self) -> u8 {
        match self {
            CarbonSignal::Green => 0,
            CarbonSignal::Yellow => 1,
            CarbonSignal::Red => 2,
        }
    }
}

/// Carbon provider error.
#[derive(Debug, Clone, PartialEq)]
pub enum CarbonError {
    /// Region is not supported by this provider.
    UnsupportedRegion { region: SmolStr },

    /// Provider returned unusable data.
    InvalidData { message: String },

    /// Provider request failed.
    ProviderFailure { provider: String, message: String },
}

impl fmt::Display for CarbonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CarbonError::UnsupportedRegion { region } => {
                write!(f, "unsupported region: {}", region)
            }
            CarbonError::InvalidData { message } => write!(f, "invalid provider data: {}", message),
            CarbonError::ProviderFailure { provider, message } => {
                write!(f, "provider {} failed: {}", provider, message)
            }
        }
    }
}

impl Error for CarbonError {}

/// Abstraction over carbon intensity data providers.
pub trait CarbonProvider: Send + Sync {
    /// Provider name for diagnostics.
    fn name(&self) -> &'static str;

    /// Whether the provider supports the given region.
    fn supports_region(&self, region: &str) -> bool;

    /// Get current carbon intensity for a region in gCO2e/kWh.
    fn get_intensity(&self, region: &str) -> Result<f64, CarbonError>;

    /// Get forecast for `hours` ahead.
    fn get_forecast(&self, region: &str, hours: u32) -> Result<Vec<CarbonForecast>, CarbonError>;
}

/// Simple in-memory provider for tests and deterministic local execution.
#[derive(Debug, Clone)]
pub struct StaticCarbonProvider {
    name: &'static str,
    intensities: FxHashMap<SmolStr, f64>,
    forecast_template: Vec<f64>,
}

impl StaticCarbonProvider {
    /// Create an empty static provider.
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            intensities: FxHashMap::default(),
            forecast_template: Vec::new(),
        }
    }

    /// Insert a region intensity value.
    pub fn with_region(mut self, region: &str, intensity: f64) -> Self {
        self.set_intensity(region, intensity);
        self
    }

    /// Set a region intensity value.
    pub fn set_intensity(&mut self, region: &str, intensity: f64) {
        self.intensities
            .insert(SmolStr::new(region), intensity.max(0.0));
    }

    /// Set a repeating forecast template in gCO2e/kWh.
    pub fn set_forecast_template(&mut self, template: Vec<f64>) {
        self.forecast_template = template.into_iter().map(|value| value.max(0.0)).collect();
    }
}

impl CarbonProvider for StaticCarbonProvider {
    fn name(&self) -> &'static str {
        self.name
    }

    fn supports_region(&self, region: &str) -> bool {
        self.intensities.contains_key(region)
    }

    fn get_intensity(&self, region: &str) -> Result<f64, CarbonError> {
        self.intensities
            .get(region)
            .copied()
            .ok_or_else(|| CarbonError::UnsupportedRegion {
                region: SmolStr::new(region),
            })
    }

    fn get_forecast(&self, region: &str, hours: u32) -> Result<Vec<CarbonForecast>, CarbonError> {
        if !self.supports_region(region) {
            return Err(CarbonError::UnsupportedRegion {
                region: SmolStr::new(region),
            });
        }

        if hours == 0 {
            return Ok(Vec::new());
        }

        let now = current_timestamp();
        let current = self.get_intensity(region)?;

        let mut out = Vec::with_capacity(hours as usize);
        for idx in 0..hours {
            let intensity = if self.forecast_template.is_empty() {
                current
            } else {
                let offset = idx as usize % self.forecast_template.len();
                self.forecast_template[offset]
            };
            out.push(CarbonForecast {
                timestamp: now + (idx as u64 + 1) * 3600,
                intensity_gco2e_per_kwh: intensity,
                confidence: 0.95,
            });
        }

        Ok(out)
    }
}

/// Local heuristic provider used as an always-available fallback.
#[derive(Debug, Clone)]
pub struct LocalHeuristicProvider {
    default_intensity: f64,
}

impl LocalHeuristicProvider {
    /// Create the default fallback provider.
    pub fn new() -> Self {
        Self {
            default_intensity: 400.0,
        }
    }

    /// Estimate intensity for a region and hour-of-day (UTC).
    pub fn estimate_intensity_at(&self, region: &str, hour_utc: u32) -> f64 {
        let base = self.region_base_intensity(region);
        let time_factor = match hour_utc {
            10..=14 => 0.7,
            6..=9 | 15..=18 => 0.85,
            19..=22 => 1.2,
            _ => 1.0,
        };

        base * time_factor
    }

    fn region_base_intensity(&self, region: &str) -> f64 {
        let region = region.to_ascii_lowercase();

        // Heuristic tags based on region naming conventions.
        if region.contains("norway")
            || region.contains("iceland")
            || region.contains("hydro")
            || region.contains("renewable")
        {
            50.0
        } else if region.contains("coal")
            || region.contains("poland")
            || region.contains("india")
            || region.contains("lignite")
        {
            600.0
        } else if region.contains("us")
            || region.contains("uk")
            || region.contains("eu")
            || region.contains("grid")
            || region.contains("mixed")
        {
            300.0
        } else {
            self.default_intensity
        }
    }

    fn hour_for_timestamp(timestamp_secs: u64) -> u32 {
        ((timestamp_secs / 3600) % 24) as u32
    }
}

impl Default for LocalHeuristicProvider {
    fn default() -> Self {
        Self::new()
    }
}

impl CarbonProvider for LocalHeuristicProvider {
    fn name(&self) -> &'static str {
        "local-heuristic"
    }

    fn supports_region(&self, _region: &str) -> bool {
        true
    }

    fn get_intensity(&self, region: &str) -> Result<f64, CarbonError> {
        let now = current_timestamp();
        let hour = Self::hour_for_timestamp(now);
        Ok(self.estimate_intensity_at(region, hour))
    }

    fn get_forecast(&self, region: &str, hours: u32) -> Result<Vec<CarbonForecast>, CarbonError> {
        if hours == 0 {
            return Ok(Vec::new());
        }

        let now = current_timestamp();
        let mut out = Vec::with_capacity(hours as usize);
        for idx in 0..hours {
            let ts = now + (idx as u64 + 1) * 3600;
            let hour = Self::hour_for_timestamp(ts);
            out.push(CarbonForecast {
                timestamp: ts,
                intensity_gco2e_per_kwh: self.estimate_intensity_at(region, hour),
                confidence: 0.5,
            });
        }
        Ok(out)
    }
}

#[derive(Debug, Clone)]
struct CachedIntensity {
    intensity: f64,
    fetched_at: u64,
}

/// Carbon intensity monitor.
pub struct CarbonMonitor {
    /// Current intensity reading.
    current: Option<CarbonReading>,

    /// Historical readings (ring buffer, max 168 = 1 week of hourly).
    history: Vec<CarbonReading>,

    /// Maximum history entries.
    max_history: usize,

    /// Green threshold (below this = Green signal).
    green_threshold: f64,

    /// Red threshold (above this = Red signal).
    red_threshold: f64,

    /// Default region.
    default_region: SmolStr,

    /// Data providers queried in order.
    providers: Vec<Box<dyn CarbonProvider>>,

    /// Cache TTL in seconds.
    cache_ttl_secs: u64,

    /// Intensity cache keyed by region.
    cache: FxHashMap<SmolStr, CachedIntensity>,

    /// Offline fallback estimator.
    fallback: LocalHeuristicProvider,
}

impl CarbonMonitor {
    /// Create a new carbon monitor with global defaults and no external providers.
    pub fn new() -> Self {
        Self::with_providers(Vec::new())
    }

    /// Create a monitor with providers in priority order.
    pub fn with_providers(providers: Vec<Box<dyn CarbonProvider>>) -> Self {
        Self {
            current: None,
            history: Vec::new(),
            max_history: 168,
            green_threshold: 200.0, // gCO2e/kWh
            red_threshold: 500.0,   // gCO2e/kWh
            default_region: SmolStr::new("global"),
            providers,
            cache_ttl_secs: 900,
            cache: FxHashMap::default(),
            fallback: LocalHeuristicProvider::new(),
        }
    }

    /// Add a provider at the end of the fallback chain.
    pub fn add_provider(&mut self, provider: Box<dyn CarbonProvider>) {
        self.providers.push(provider);
    }

    /// Number of configured providers.
    pub fn provider_count(&self) -> usize {
        self.providers.len()
    }

    /// Set cache TTL in seconds.
    pub fn set_cache_ttl_secs(&mut self, ttl_secs: u64) {
        self.cache_ttl_secs = ttl_secs;
    }

    /// Set thresholds for carbon signal decisions.
    pub fn set_thresholds(&mut self, green: f64, red: f64) {
        self.green_threshold = green;
        self.red_threshold = red;
    }

    /// Update the current carbon intensity reading.
    pub fn update_intensity(&mut self, region: SmolStr, intensity: f64) {
        if !intensity.is_finite() || intensity < 0.0 {
            return;
        }

        let reading = CarbonReading {
            region: region.clone(),
            intensity_gco2e_per_kwh: intensity,
            timestamp: current_timestamp(),
        };

        // Archive the old reading.
        if let Some(old) = self.current.take() {
            self.history.push(old);
            if self.history.len() > self.max_history {
                self.history.remove(0);
            }
        }

        self.cache.insert(
            region,
            CachedIntensity {
                intensity,
                fetched_at: reading.timestamp,
            },
        );

        self.current = Some(reading);
    }

    /// Fetch intensity from providers (with cache and local fallback).
    pub fn fetch_intensity(&mut self, region: &str) -> f64 {
        let now = current_timestamp();
        let region_key = SmolStr::new(region);

        if let Some(cached) = self.cache.get(&region_key) {
            if now.saturating_sub(cached.fetched_at) <= self.cache_ttl_secs {
                return cached.intensity;
            }
        }

        for provider in &self.providers {
            if !provider.supports_region(region) {
                continue;
            }

            let Ok(intensity) = provider.get_intensity(region) else {
                continue;
            };

            if intensity.is_finite() && intensity >= 0.0 {
                self.update_intensity(region_key.clone(), intensity);
                return intensity;
            }
        }

        let fallback = self
            .fallback
            .get_intensity(region)
            .unwrap_or(self.default_region_intensity());

        self.update_intensity(region_key, fallback);
        fallback
    }

    /// Get forecast using providers with local fallback.
    pub fn forecast(&self, region: &str, hours: u32) -> Vec<CarbonForecast> {
        if hours == 0 {
            return Vec::new();
        }

        for provider in &self.providers {
            if !provider.supports_region(region) {
                continue;
            }

            if let Ok(points) = provider.get_forecast(region, hours) {
                if !points.is_empty() {
                    return points;
                }
            }
        }

        self.fallback
            .get_forecast(region, hours)
            .unwrap_or_default()
    }

    /// Get the current carbon signal.
    pub fn signal(&self) -> CarbonSignal {
        match &self.current {
            Some(reading) => {
                if reading.intensity_gco2e_per_kwh <= self.green_threshold {
                    CarbonSignal::Green
                } else if reading.intensity_gco2e_per_kwh >= self.red_threshold {
                    CarbonSignal::Red
                } else {
                    CarbonSignal::Yellow
                }
            }
            // No data: assume moderate.
            None => CarbonSignal::Yellow,
        }
    }

    /// Get current intensity value (or 0.0 if unknown).
    pub fn current_intensity(&self) -> f64 {
        self.current
            .as_ref()
            .map(|r| r.intensity_gco2e_per_kwh)
            .unwrap_or(0.0)
    }

    /// Get current reading, if present.
    pub fn current_reading(&self) -> Option<&CarbonReading> {
        self.current.as_ref()
    }

    /// Average intensity over history window.
    pub fn average_intensity(&self) -> f64 {
        if self.history.is_empty() {
            return self.current_intensity();
        }
        let sum: f64 = self.history.iter().map(|r| r.intensity_gco2e_per_kwh).sum();
        let count = self.history.len() as f64;
        sum / count
    }

    /// Whether now is a good time to defer deferrable workloads.
    pub fn should_defer(&self) -> bool {
        self.signal() == CarbonSignal::Red
    }

    /// Estimate carbon cost (gCO2e) for the given energy usage (Joules).
    pub fn estimate_carbon(&self, energy_joules: f64) -> f64 {
        let kwh = energy_joules / 3_600_000.0;
        kwh * self.current_intensity()
    }

    /// Get the default region.
    pub fn region(&self) -> &SmolStr {
        &self.default_region
    }

    /// Set the default region.
    pub fn set_region(&mut self, region: SmolStr) {
        self.default_region = region;
    }

    /// Number of historical readings.
    pub fn history_len(&self) -> usize {
        self.history.len()
    }

    fn default_region_intensity(&self) -> f64 {
        self.current_intensity()
            .max(self.fallback.default_intensity)
    }
}

impl Default for CarbonMonitor {
    fn default() -> Self {
        Self::new()
    }
}

fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
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
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    struct CountingProvider {
        calls: Arc<AtomicUsize>,
        intensity: f64,
    }

    impl CarbonProvider for CountingProvider {
        fn name(&self) -> &'static str {
            "counting"
        }

        fn supports_region(&self, region: &str) -> bool {
            region == "cache-zone"
        }

        fn get_intensity(&self, _region: &str) -> Result<f64, CarbonError> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            Ok(self.intensity)
        }

        fn get_forecast(
            &self,
            _region: &str,
            _hours: u32,
        ) -> Result<Vec<CarbonForecast>, CarbonError> {
            Err(CarbonError::ProviderFailure {
                provider: "counting".to_string(),
                message: "forecast unsupported".to_string(),
            })
        }
    }

    #[test]
    fn test_default_signal_is_yellow() {
        let monitor = CarbonMonitor::new();
        assert_eq!(monitor.signal(), CarbonSignal::Yellow);
    }

    #[test]
    fn test_green_signal() {
        let mut monitor = CarbonMonitor::new();
        monitor.update_intensity(SmolStr::new("uk"), 150.0);
        assert_eq!(monitor.signal(), CarbonSignal::Green);
    }

    #[test]
    fn test_red_signal() {
        let mut monitor = CarbonMonitor::new();
        monitor.update_intensity(SmolStr::new("coal-region"), 600.0);
        assert_eq!(monitor.signal(), CarbonSignal::Red);
        assert!(monitor.should_defer());
    }

    #[test]
    fn test_yellow_signal() {
        let mut monitor = CarbonMonitor::new();
        monitor.update_intensity(SmolStr::new("mixed"), 350.0);
        assert_eq!(monitor.signal(), CarbonSignal::Yellow);
        assert!(!monitor.should_defer());
    }

    #[test]
    fn test_carbon_estimation() {
        let mut monitor = CarbonMonitor::new();
        monitor.update_intensity(SmolStr::new("uk"), 400.0);
        // 1 kWh = 3,600,000 J -> 400 gCO2e
        let carbon = monitor.estimate_carbon(3_600_000.0);
        assert!((carbon - 400.0).abs() < 0.01);
    }

    #[test]
    fn test_history_tracking() {
        let mut monitor = CarbonMonitor::new();
        monitor.update_intensity(SmolStr::new("r"), 100.0);
        monitor.update_intensity(SmolStr::new("r"), 200.0);
        monitor.update_intensity(SmolStr::new("r"), 300.0);

        // First two readings are in history, third is current.
        assert_eq!(monitor.history_len(), 2);
        assert!((monitor.average_intensity() - 150.0).abs() < 0.01);
    }

    #[test]
    fn test_custom_thresholds() {
        let mut monitor = CarbonMonitor::new();
        monitor.set_thresholds(100.0, 300.0);
        monitor.update_intensity(SmolStr::new("x"), 250.0);
        assert_eq!(monitor.signal(), CarbonSignal::Yellow);
        monitor.update_intensity(SmolStr::new("x"), 50.0);
        assert_eq!(monitor.signal(), CarbonSignal::Green);
    }

    #[test]
    fn test_fetch_uses_provider_cache() {
        let calls = Arc::new(AtomicUsize::new(0));
        let provider = CountingProvider {
            calls: calls.clone(),
            intensity: 180.0,
        };

        let mut monitor = CarbonMonitor::with_providers(vec![Box::new(provider)]);
        monitor.set_cache_ttl_secs(60);

        let i1 = monitor.fetch_intensity("cache-zone");
        let i2 = monitor.fetch_intensity("cache-zone");

        assert_eq!(i1, 180.0);
        assert_eq!(i2, 180.0);
        assert_eq!(calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_fetch_falls_back_when_provider_unsupported() {
        let mut monitor =
            CarbonMonitor::with_providers(vec![Box::new(StaticCarbonProvider::new("static"))]);

        let value = monitor.fetch_intensity("unknown-zone");
        assert!(value > 0.0);
        assert!(matches!(
            monitor.signal(),
            CarbonSignal::Green | CarbonSignal::Yellow | CarbonSignal::Red
        ));
    }

    #[test]
    fn test_forecast_local_fallback() {
        let monitor = CarbonMonitor::new();
        let points = monitor.forecast("global", 6);
        assert_eq!(points.len(), 6);
        assert!(points.iter().all(|p| p.intensity_gco2e_per_kwh >= 0.0));
    }

    #[test]
    fn test_local_heuristic_evening_higher_than_noon_for_mixed_grid() {
        let fallback = LocalHeuristicProvider::new();
        let noon = fallback.estimate_intensity_at("us-grid", 12);
        let evening = fallback.estimate_intensity_at("us-grid", 20);
        assert!(evening > noon);
    }

    #[test]
    fn test_static_provider_forecast_template_cycles() {
        let mut provider = StaticCarbonProvider::new("static").with_region("uk", 200.0);
        provider.set_forecast_template(vec![100.0, 200.0, 300.0]);

        let points = expect_ok(provider.get_forecast("uk", 5));
        let got: Vec<f64> = points.iter().map(|p| p.intensity_gco2e_per_kwh).collect();

        assert_eq!(got, vec![100.0, 200.0, 300.0, 100.0, 200.0]);
    }
}
