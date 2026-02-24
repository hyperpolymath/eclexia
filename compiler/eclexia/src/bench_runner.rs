// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Benchmark runner for Eclexia programs.

use eclexia_ast::{Attribute, Item, SourceFile};
use eclexia_codegen::{Backend, BytecodeGenerator, VirtualMachine};
use std::fs;
use std::path::Path;
use std::time::{Duration, Instant};

/// A benchmark function with metadata.
#[derive(Debug)]
pub struct BenchFunction {
    pub name: String,
    pub attributes: Vec<Attribute>,
}

/// Energy measurement from RAPL (Running Average Power Limit).
///
/// Reads Intel RAPL counters from sysfs to measure energy consumption
/// of benchmark runs. Available on Linux with Intel CPUs.
#[derive(Debug, Clone)]
pub struct EnergyMeasurement {
    /// Total energy consumed in Joules.
    pub joules: f64,
    /// Energy per iteration in Joules.
    pub joules_per_iter: f64,
    /// Estimated power draw in Watts.
    pub watts: f64,
    /// Estimated carbon cost in gCO2e (using grid carbon intensity).
    pub gco2e: f64,
    /// RAPL domain measured (e.g., "package-0", "core", "dram").
    pub domain: String,
}

/// RAPL energy reader.
///
/// Reads energy counters from /sys/class/powercap/intel-rapl/
/// to measure actual hardware energy consumption.
struct RaplReader {
    /// Path to the RAPL energy counter file.
    energy_path: String,
    /// RAPL domain name.
    domain: String,
    /// Max energy range in microjoules (for wraparound detection).
    max_energy_uj: u64,
}

impl RaplReader {
    /// Discover available RAPL domains and return readers.
    fn discover() -> Vec<Self> {
        let base = "/sys/class/powercap/intel-rapl";
        let mut readers = Vec::new();

        // Try intel-rapl:0 (package-0), intel-rapl:0:0 (core), intel-rapl:0:2 (dram)
        for entry in &["intel-rapl:0", "intel-rapl:0:0", "intel-rapl:0:2"] {
            let energy_path = format!("{}/{}/energy_uj", base, entry);
            let name_path = format!("{}/{}/name", base, entry);
            let max_path = format!("{}/{}/max_energy_range_uj", base, entry);

            if Path::new(&energy_path).exists() {
                let domain = fs::read_to_string(&name_path)
                    .unwrap_or_else(|_| entry.to_string())
                    .trim()
                    .to_string();

                let max_energy_uj = fs::read_to_string(&max_path)
                    .ok()
                    .and_then(|s| s.trim().parse::<u64>().ok())
                    .unwrap_or(u64::MAX);

                readers.push(RaplReader {
                    energy_path,
                    domain,
                    max_energy_uj,
                });
            }
        }

        readers
    }

    /// Read current energy counter in microjoules.
    fn read_energy_uj(&self) -> Option<u64> {
        fs::read_to_string(&self.energy_path)
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
    }

    /// Compute energy difference handling wraparound.
    fn energy_diff_uj(&self, before: u64, after: u64) -> u64 {
        if after >= before {
            after - before
        } else {
            // Counter wrapped around
            (self.max_energy_uj - before) + after
        }
    }
}

/// Grid carbon intensity in gCO2e per kWh.
///
/// This is an average value. For real-time data, integrate with
/// electricityMap or WattTime APIs.
const DEFAULT_GRID_CARBON_INTENSITY: f64 = 400.0; // gCO2e/kWh, global average

/// Benchmark statistics.
#[derive(Debug)]
#[allow(dead_code)]
pub struct BenchStats {
    pub iterations: usize,
    pub total_time: Duration,
    pub mean: Duration,
    pub median: Duration,
    pub min: Duration,
    pub max: Duration,
    pub std_dev: f64,
    /// Energy measurements (empty if --energy not enabled or RAPL unavailable).
    pub energy: Vec<EnergyMeasurement>,
}

impl BenchStats {
    fn from_samples(samples: &[Duration], energy: Vec<EnergyMeasurement>) -> Self {
        let mut sorted = samples.to_vec();
        sorted.sort();

        let total_time: Duration = samples.iter().sum();
        let mean = total_time / samples.len() as u32;
        let median = sorted[samples.len() / 2];
        let min = sorted[0];
        let max = sorted[samples.len() - 1];

        // Calculate standard deviation
        let mean_nanos = mean.as_nanos() as f64;
        let variance: f64 = samples
            .iter()
            .map(|d| {
                let diff = d.as_nanos() as f64 - mean_nanos;
                diff * diff
            })
            .sum::<f64>()
            / samples.len() as f64;
        let std_dev = variance.sqrt();

        BenchStats {
            iterations: samples.len(),
            total_time,
            mean,
            median,
            min,
            max,
            std_dev,
            energy,
        }
    }
}

/// Benchmark result.
#[derive(Debug)]
#[allow(dead_code)]
pub enum BenchResult {
    Success(BenchStats),
    Failed { error: String },
    Ignored,
}

/// Benchmark summary statistics.
#[derive(Debug, Default)]
pub struct BenchSummary {
    pub benchmarks_run: usize,
    pub benchmarks_failed: usize,
    pub benchmarks_ignored: usize,
}

/// Collect all benchmark functions from a source file.
pub fn collect_benchmarks(file: &SourceFile) -> Vec<BenchFunction> {
    let mut benches = Vec::new();

    for item in &file.items {
        if let Item::Function(func) = item {
            if has_bench_attribute(&func.attributes) {
                benches.push(BenchFunction {
                    name: func.name.to_string(),
                    attributes: func.attributes.clone(),
                });
            }
        }
    }

    benches
}

/// Check if attributes contain #[bench]
fn has_bench_attribute(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attr| attr.name == "bench")
}

/// Check if attributes contain #[ignore]
fn has_ignore_attribute(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attr| attr.name == "ignore")
}

/// Run a single benchmark function.
pub fn run_benchmark(
    file: &SourceFile,
    bench: &BenchFunction,
    iterations: usize,
    verbose: bool,
    energy_enabled: bool,
) -> BenchResult {
    if has_ignore_attribute(&bench.attributes) {
        if verbose {
            println!("bench {} ... ignored", bench.name);
        }
        return BenchResult::Ignored;
    }

    // Type check
    let type_errors = eclexia_typeck::check(file);
    if !type_errors.is_empty() {
        return BenchResult::Failed {
            error: format!("Type checking failed: {:?}", type_errors),
        };
    }

    // Lower to HIR
    let hir = eclexia_hir::lower_source_file(file);

    // Lower to MIR
    let mir = eclexia_mir::lower_hir_file(&hir);

    // Generate bytecode
    let mut codegen = BytecodeGenerator::new();
    let bytecode = match codegen.generate(&mir) {
        Ok(bc) => bc,
        Err(e) => {
            return BenchResult::Failed {
                error: format!("Codegen failed: {}", e),
            };
        }
    };

    // Find the benchmark function in the bytecode
    let bench_fn_index = bytecode.functions.iter().position(|f| f.name == bench.name);

    if bench_fn_index.is_none() {
        return BenchResult::Failed {
            error: format!("Benchmark function '{}' not found in bytecode", bench.name),
        };
    }

    // Discover RAPL readers if energy measurement is enabled
    let rapl_readers = if energy_enabled {
        RaplReader::discover()
    } else {
        Vec::new()
    };

    // Read initial RAPL energy counters
    let energy_before: Vec<(String, u64)> = rapl_readers
        .iter()
        .filter_map(|r| r.read_energy_uj().map(|uj| (r.domain.clone(), uj)))
        .collect();

    // Run the benchmark multiple times to collect timing samples
    let mut samples = Vec::with_capacity(iterations);

    for _ in 0..iterations {
        let mut vm = VirtualMachine::new(bytecode.clone());
        let start = Instant::now();

        match vm.run() {
            Ok(_) => {
                let elapsed = start.elapsed();
                samples.push(elapsed);
            }
            Err(e) => {
                return BenchResult::Failed {
                    error: format!("Runtime error: {}", e),
                };
            }
        }
    }

    // Read final RAPL energy counters and compute energy measurements
    let energy_measurements = if energy_enabled && !rapl_readers.is_empty() {
        let total_secs = samples.iter().map(|d| d.as_secs_f64()).sum::<f64>();

        rapl_readers
            .iter()
            .zip(energy_before.iter())
            .filter_map(|(reader, (domain, before_uj))| {
                reader.read_energy_uj().map(|after_uj| {
                    let diff_uj = reader.energy_diff_uj(*before_uj, after_uj);
                    let joules = diff_uj as f64 / 1_000_000.0;
                    let joules_per_iter = joules / iterations as f64;
                    let watts = if total_secs > 0.0 {
                        joules / total_secs
                    } else {
                        0.0
                    };

                    // Carbon estimation: convert Joules to kWh, multiply by grid intensity
                    let kwh = joules / 3_600_000.0;
                    let gco2e = kwh * DEFAULT_GRID_CARBON_INTENSITY;

                    EnergyMeasurement {
                        joules,
                        joules_per_iter,
                        watts,
                        gco2e,
                        domain: domain.clone(),
                    }
                })
            })
            .collect()
    } else {
        Vec::new()
    };

    let stats = BenchStats::from_samples(&samples, energy_measurements);

    if verbose {
        println!(
            "bench {} ... {} iterations, {:.2?} avg, {:.2?} median",
            bench.name, stats.iterations, stats.mean, stats.median
        );

        for em in &stats.energy {
            println!(
                "  energy [{}]: {:.6} J total, {:.9} J/iter, {:.2} W, {:.6} gCO2e",
                em.domain, em.joules, em.joules_per_iter, em.watts, em.gco2e
            );
        }
    }

    BenchResult::Success(stats)
}

/// Run all benchmarks and return summary.
pub fn run_all_benchmarks(
    file: &SourceFile,
    filter: Option<&str>,
    iterations: usize,
    verbose: bool,
    energy_enabled: bool,
) -> BenchSummary {
    let benches = collect_benchmarks(file);

    let filtered_benches: Vec<_> = if let Some(pattern) = filter {
        benches
            .into_iter()
            .filter(|b| b.name.contains(pattern))
            .collect()
    } else {
        benches
    };

    if filtered_benches.is_empty() {
        println!("No benchmarks found");
        return BenchSummary::default();
    }

    println!("\nrunning {} benchmarks", filtered_benches.len());

    if energy_enabled {
        let rapl_available = !RaplReader::discover().is_empty();
        if rapl_available {
            println!("energy measurement: RAPL enabled");
        } else {
            println!("energy measurement: RAPL not available (no /sys/class/powercap/intel-rapl/)");
        }
    }

    let mut summary = BenchSummary::default();

    for bench in &filtered_benches {
        let result = run_benchmark(file, bench, iterations, verbose, energy_enabled);

        match result {
            BenchResult::Success(_) => {
                summary.benchmarks_run += 1;
            }
            BenchResult::Failed { .. } => {
                summary.benchmarks_failed += 1;
            }
            BenchResult::Ignored => {
                summary.benchmarks_ignored += 1;
            }
        }
    }

    // Print summary
    println!(
        "\nbenchmark result: {}. {} benchmarks run; {} failed; {} ignored\n",
        if summary.benchmarks_failed == 0 {
            "ok"
        } else {
            "FAILED"
        },
        summary.benchmarks_run,
        summary.benchmarks_failed,
        summary.benchmarks_ignored
    );

    summary
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_bench_attribute() {
        use eclexia_ast::span::Span;
        use smol_str::SmolStr;

        let attrs = vec![Attribute {
            span: Span::new(0, 0),
            name: SmolStr::new("bench"),
            args: vec![],
        }];

        assert!(has_bench_attribute(&attrs));
    }

    #[test]
    fn test_bench_stats_calculation() {
        let samples = vec![
            Duration::from_micros(100),
            Duration::from_micros(150),
            Duration::from_micros(120),
            Duration::from_micros(130),
            Duration::from_micros(140),
        ];

        let stats = BenchStats::from_samples(&samples, vec![]);

        assert_eq!(stats.iterations, 5);
        assert_eq!(stats.min, Duration::from_micros(100));
        assert_eq!(stats.max, Duration::from_micros(150));
        assert_eq!(stats.median, Duration::from_micros(130));
        assert!(stats.energy.is_empty());
    }

    #[test]
    fn test_bench_stats_with_energy() {
        let samples = vec![Duration::from_millis(10), Duration::from_millis(12)];

        let energy = vec![EnergyMeasurement {
            joules: 0.5,
            joules_per_iter: 0.25,
            watts: 22.7,
            gco2e: 0.0000556,
            domain: "package-0".to_string(),
        }];

        let stats = BenchStats::from_samples(&samples, energy);
        assert_eq!(stats.energy.len(), 1);
        assert!((stats.energy[0].joules - 0.5).abs() < 1e-10);
        assert_eq!(stats.energy[0].domain, "package-0");
    }

    #[test]
    fn test_rapl_energy_diff_no_wraparound() {
        let reader = RaplReader {
            energy_path: String::new(),
            domain: "test".to_string(),
            max_energy_uj: 1_000_000,
        };
        assert_eq!(reader.energy_diff_uj(100, 500), 400);
    }

    #[test]
    fn test_rapl_energy_diff_wraparound() {
        let reader = RaplReader {
            energy_path: String::new(),
            domain: "test".to_string(),
            max_energy_uj: 1_000_000,
        };
        // Counter wrapped: was at 999_000, now at 500
        assert_eq!(reader.energy_diff_uj(999_000, 500), 1_500);
    }

    #[test]
    fn test_carbon_estimation() {
        // 1 kWh = 3_600_000 J
        // At 400 gCO2e/kWh, 1 J = 400/3_600_000 gCO2e
        let joules = 3_600.0; // 0.001 kWh
        let kwh = joules / 3_600_000.0;
        let gco2e = kwh * DEFAULT_GRID_CARBON_INTENSITY;
        assert!((gco2e - 0.4).abs() < 1e-6);
    }
}
