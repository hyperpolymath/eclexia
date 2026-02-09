// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Carbon intensity monitor and scheduler.
//!
//! Tracks grid carbon intensity and provides scheduling signals so that
//! deferrable workloads can be shifted to lower-carbon time windows.
//! Uses a simple model: intensity values are set externally (e.g. from
//! an API or config) and the monitor provides threshold-based decisions.

use smol_str::SmolStr;
use std::time::{SystemTime, UNIX_EPOCH};

/// Carbon intensity reading.
#[derive(Debug, Clone)]
pub struct CarbonReading {
    /// Grid region identifier.
    pub region: SmolStr,

    /// Carbon intensity in gCO2e per kWh.
    pub intensity_gco2e_per_kwh: f64,

    /// Timestamp when this reading was taken.
    pub timestamp: u64,
}

/// Scheduling signal based on carbon intensity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CarbonSignal {
    /// Intensity is low — good time to run workloads.
    Green,

    /// Intensity is moderate — run if needed.
    Yellow,

    /// Intensity is high — defer non-essential work.
    Red,
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
}

impl CarbonMonitor {
    /// Create a new carbon monitor with global average defaults.
    pub fn new() -> Self {
        Self {
            current: None,
            history: Vec::new(),
            max_history: 168,
            green_threshold: 200.0,  // gCO2e/kWh
            red_threshold: 500.0,    // gCO2e/kWh
            default_region: SmolStr::new("global"),
        }
    }

    /// Set thresholds for carbon signal decisions.
    pub fn set_thresholds(&mut self, green: f64, red: f64) {
        self.green_threshold = green;
        self.red_threshold = red;
    }

    /// Update the current carbon intensity reading.
    pub fn update_intensity(&mut self, region: SmolStr, intensity: f64) {
        let reading = CarbonReading {
            region,
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

        self.current = Some(reading);
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
            // No data — assume moderate.
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

    /// Average intensity over history window.
    pub fn average_intensity(&self) -> f64 {
        if self.history.is_empty() {
            return self.current_intensity();
        }
        let sum: f64 = self
            .history
            .iter()
            .map(|r| r.intensity_gco2e_per_kwh)
            .sum();
        let count = self.history.len() as f64;
        sum / count
    }

    /// Whether now is a good time to run deferrable workloads.
    pub fn should_defer(&self) -> bool {
        self.signal() == CarbonSignal::Red
    }

    /// Estimate carbon cost for a given energy consumption.
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
        // 1 kWh = 3,600,000 J → 400 gCO2e
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
}
