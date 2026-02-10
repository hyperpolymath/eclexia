// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Simple access to system power metrics (e.g., RAPL energy counters).

use std::fs;
use std::io;
use std::path::Path;
use std::time::Instant;

const RAPL_PATHS: &[&str] = &[
    "/sys/class/powercap/intel-rapl:0/energy_uj",
    "/sys/class/powercap/intel-rapl:0:0/energy_uj",
];

/// Power sample snapshot.
#[derive(Debug, Clone)]
pub struct PowerSample {
    /// Energy delta in joules.
    pub energy_joules: f64,

    /// Time delta in seconds.
    pub duration_secs: f64,

    /// Estimated carbon emissions in grams (derived from energy).
    pub carbon_gco2e: f64,

    /// Timestamp of the sample.
    pub timestamp: Instant,
}

/// RAPL-based power metrics tracker.
pub struct PowerMetrics {
    last_reading: Option<(u64, Instant)>,
    carbon_factor: f64,
}

impl PowerMetrics {
    /// Create a new metrics tracker.
    pub fn new() -> Self {
        Self {
            last_reading: None,
            carbon_factor: 0.0004, // 0.4 gCO2 per Joule (baseline)
        }
    }

    /// Attempt to sample the energy counter.
    pub fn sample(&mut self) -> Option<PowerSample> {
        let now = Instant::now();
        let raw = Self::read_energy().ok()?;

        if let Some((prev_value, prev_time)) = self.last_reading.replace((raw, now)) {
            let delta = raw.saturating_sub(prev_value);
            let duration_secs = now.duration_since(prev_time).as_secs_f64();
            if duration_secs <= 0.0 || delta == 0 {
                return None;
            }

            let energy_joules = (delta as f64) / 1_000_000.0;
            let carbon_gco2e = energy_joules * self.carbon_factor;

            Some(PowerSample {
                energy_joules,
                duration_secs,
                carbon_gco2e,
                timestamp: now,
            })
        } else {
            None
        }
    }

    /// Check whether the underlying sensor is available.
    pub fn is_available() -> bool {
        RAPL_PATHS.iter().any(|path| Path::new(path).exists())
    }

    fn read_energy() -> io::Result<u64> {
        for path in RAPL_PATHS {
            if let Ok(data) = fs::read_to_string(path) {
                if let Ok(value) = data.trim().parse::<u64>() {
                    return Ok(value);
                }
            }
        }
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            "RAPL energy counter not accessible",
        ))
    }
}
