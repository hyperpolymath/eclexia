// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Resource profiler for tracking energy, time, memory, carbon.
//!
//! Instruments code regions to measure actual resource consumption and
//! feeds measurements back to the shadow price registry for calibration.

use eclexia_ast::dimension::Dimension;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::time::Instant;

/// A profiling span measuring resource consumption of a code region.
#[derive(Debug, Clone)]
pub struct ProfileSpan {
    /// Span name (function or block identifier).
    pub name: SmolStr,

    /// Wall-clock duration in seconds.
    pub wall_time_s: f64,

    /// Estimated energy in Joules (derived from time * power model).
    pub energy_j: f64,

    /// Peak memory delta in bytes (if tracked).
    pub memory_bytes: f64,

    /// Carbon estimate in gCO2e (energy * grid intensity).
    pub carbon_gco2e: f64,

    /// Call count for this span.
    pub call_count: u64,
}

/// Active (in-flight) profiling measurement.
struct ActiveSpan {
    name: SmolStr,
    start: Instant,
    memory_before: f64, // RSS in bytes at span start
}

/// Aggregated profile data per function/block.
#[derive(Debug, Clone)]
struct SpanAggregate {
    total_wall_time_s: f64,
    total_energy_j: f64,
    total_memory_bytes: f64,
    total_carbon_gco2e: f64,
    call_count: u64,
}

/// Resource profiler.
pub struct Profiler {
    /// Stack of active spans (supports nested profiling).
    active: Vec<ActiveSpan>,

    /// Aggregated data keyed by span name.
    aggregates: HashMap<SmolStr, SpanAggregate>,

    /// Assumed average power draw in Watts for energy estimation.
    power_model_watts: f64,

    /// Current grid carbon intensity in gCO2e/kWh.
    carbon_intensity_gco2e_per_kwh: f64,

    /// Whether profiling is enabled.
    enabled: bool,
}

/// Read current RSS (Resident Set Size) in bytes on Linux.
/// Returns 0.0 on non-Linux platforms or if reading fails.
#[cfg(target_os = "linux")]
fn get_rss_bytes() -> f64 {
    // Read /proc/self/statm which contains memory stats in pages
    // Format: size resident shared text lib data dt
    // We want field 1 (resident) which is RSS in pages
    if let Ok(contents) = std::fs::read_to_string("/proc/self/statm") {
        let fields: Vec<&str> = contents.split_whitespace().collect();
        if fields.len() > 1 {
            if let Ok(rss_pages) = fields[1].parse::<usize>() {
                // Convert pages to bytes (typically 4096 bytes per page)
                let page_size = 4096.0;
                return (rss_pages as f64) * page_size;
            }
        }
    }
    0.0
}

#[cfg(not(target_os = "linux"))]
fn get_rss_bytes() -> f64 {
    0.0 // Not supported on non-Linux platforms
}

impl Profiler {
    /// Create a new profiler.
    pub fn new() -> Self {
        Self {
            active: Vec::new(),
            aggregates: HashMap::new(),
            power_model_watts: 65.0,               // typical laptop TDP
            carbon_intensity_gco2e_per_kwh: 400.0, // global average
            enabled: true,
        }
    }

    /// Enable or disable profiling.
    pub fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    /// Set power model for energy estimation.
    pub fn set_power_model(&mut self, watts: f64) {
        self.power_model_watts = watts;
    }

    /// Set carbon intensity for emission estimates.
    pub fn set_carbon_intensity(&mut self, gco2e_per_kwh: f64) {
        self.carbon_intensity_gco2e_per_kwh = gco2e_per_kwh;
    }

    /// Begin profiling a named span.
    pub fn begin_span(&mut self, name: SmolStr) {
        if !self.enabled {
            return;
        }
        self.active.push(ActiveSpan {
            name,
            start: Instant::now(),
            memory_before: get_rss_bytes(),
        });
    }

    /// End the most recent span and record measurements.
    pub fn end_span(&mut self) -> Option<ProfileSpan> {
        if !self.enabled {
            return None;
        }
        let span = self.active.pop()?;
        let elapsed = span.start.elapsed();
        let wall_time_s = elapsed.as_secs_f64();

        // Energy = Power (W) * Time (s) = Joules
        let energy_j = self.power_model_watts * wall_time_s;

        // Carbon = Energy (J) / 3600000 (to kWh) * intensity (gCO2e/kWh)
        let energy_kwh = energy_j / 3_600_000.0;
        let carbon_gco2e = energy_kwh * self.carbon_intensity_gco2e_per_kwh;

        // Memory delta = RSS after - RSS before (on Linux; 0 on other platforms)
        let memory_after = get_rss_bytes();
        let memory_bytes = (memory_after - span.memory_before).max(0.0);

        let result = ProfileSpan {
            name: span.name.clone(),
            wall_time_s,
            energy_j,
            memory_bytes,
            carbon_gco2e,
            call_count: 1,
        };

        // Aggregate
        let agg = self.aggregates.entry(span.name).or_insert(SpanAggregate {
            total_wall_time_s: 0.0,
            total_energy_j: 0.0,
            total_memory_bytes: 0.0,
            total_carbon_gco2e: 0.0,
            call_count: 0,
        });
        agg.total_wall_time_s += wall_time_s;
        agg.total_energy_j += energy_j;
        agg.total_memory_bytes += memory_bytes;
        agg.total_carbon_gco2e += carbon_gco2e;
        agg.call_count += 1;

        Some(result)
    }

    /// Get aggregated profile for a span.
    pub fn get_span_profile(&self, name: &str) -> Option<ProfileSpan> {
        let agg = self.aggregates.get(name)?;
        Some(ProfileSpan {
            name: SmolStr::new(name),
            wall_time_s: agg.total_wall_time_s,
            energy_j: agg.total_energy_j,
            memory_bytes: agg.total_memory_bytes,
            carbon_gco2e: agg.total_carbon_gco2e,
            call_count: agg.call_count,
        })
    }

    /// Get all profiled spans sorted by total wall time (descending).
    pub fn all_spans(&self) -> Vec<ProfileSpan> {
        let mut spans: Vec<ProfileSpan> = self
            .aggregates
            .iter()
            .map(|(name, agg)| ProfileSpan {
                name: name.clone(),
                wall_time_s: agg.total_wall_time_s,
                energy_j: agg.total_energy_j,
                memory_bytes: agg.total_memory_bytes,
                carbon_gco2e: agg.total_carbon_gco2e,
                call_count: agg.call_count,
            })
            .collect();
        spans.sort_by(|a, b| {
            b.wall_time_s
                .partial_cmp(&a.wall_time_s)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        spans
    }

    /// Convert profile data to resource tracker dimensions for feedback.
    pub fn as_dimension_costs(&self, name: &str) -> Vec<(Dimension, f64)> {
        match self.aggregates.get(name) {
            Some(agg) => vec![
                (Dimension::energy(), agg.total_energy_j),
                (Dimension::time(), agg.total_wall_time_s),
                (Dimension::memory(), agg.total_memory_bytes),
                (Dimension::carbon(), agg.total_carbon_gco2e),
            ],
            None => vec![],
        }
    }

    /// Reset all profiling data.
    pub fn reset(&mut self) {
        self.active.clear();
        self.aggregates.clear();
    }

    /// Number of active (unclosed) spans.
    pub fn active_depth(&self) -> usize {
        self.active.len()
    }
}

impl Default for Profiler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_some<T>(value: Option<T>, context: &str) -> T {
        match value {
            Some(val) => val,
            None => panic!("Expected Some value: {}", context),
        }
    }

    #[test]
    fn test_begin_end_span() {
        let mut profiler = Profiler::new();
        profiler.begin_span(SmolStr::new("test_fn"));
        std::thread::sleep(std::time::Duration::from_millis(10));
        let span = expect_some(profiler.end_span(), "should return span");

        assert_eq!(span.name.as_str(), "test_fn");
        assert!(span.wall_time_s >= 0.009); // at least ~10ms
        assert!(span.energy_j > 0.0);
        assert!(span.carbon_gco2e > 0.0);
        assert_eq!(span.call_count, 1);
    }

    #[test]
    fn test_aggregation() {
        let mut profiler = Profiler::new();

        for _ in 0..3 {
            profiler.begin_span(SmolStr::new("hot_path"));
            profiler.end_span();
        }

        let agg = expect_some(profiler.get_span_profile("hot_path"), "should exist");
        assert_eq!(agg.call_count, 3);
    }

    #[test]
    fn test_disabled_profiler() {
        let mut profiler = Profiler::new();
        profiler.set_enabled(false);

        profiler.begin_span(SmolStr::new("noop"));
        assert!(profiler.end_span().is_none());
    }

    #[test]
    fn test_nested_spans() {
        let mut profiler = Profiler::new();
        profiler.begin_span(SmolStr::new("outer"));
        profiler.begin_span(SmolStr::new("inner"));

        let inner = expect_some(profiler.end_span(), "inner span");
        assert_eq!(inner.name.as_str(), "inner");

        let outer = expect_some(profiler.end_span(), "outer span");
        assert_eq!(outer.name.as_str(), "outer");
        assert!(outer.wall_time_s >= inner.wall_time_s);
    }

    #[test]
    fn test_dimension_costs() {
        let mut profiler = Profiler::new();
        profiler.begin_span(SmolStr::new("measured"));
        std::thread::sleep(std::time::Duration::from_millis(5));
        profiler.end_span();

        let costs = profiler.as_dimension_costs("measured");
        assert_eq!(costs.len(), 4);
    }

    #[test]
    fn test_reset() {
        let mut profiler = Profiler::new();
        profiler.begin_span(SmolStr::new("x"));
        profiler.end_span();
        profiler.reset();
        assert!(profiler.all_spans().is_empty());
    }
}
