// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Benchmark runner for Eclexia programs.

use eclexia_ast::{Attribute, Item, SourceFile};
use eclexia_codegen::{Backend, BytecodeGenerator, VirtualMachine, VmValue};
use std::time::{Duration, Instant};

/// A benchmark function with metadata.
#[derive(Debug)]
pub struct BenchFunction {
    pub name: String,
    pub attributes: Vec<Attribute>,
}

/// Benchmark statistics.
#[derive(Debug)]
pub struct BenchStats {
    pub iterations: usize,
    pub total_time: Duration,
    pub mean: Duration,
    pub median: Duration,
    pub min: Duration,
    pub max: Duration,
    pub std_dev: f64,
}

impl BenchStats {
    fn from_samples(samples: &[Duration]) -> Self {
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
        }
    }
}

/// Benchmark result.
#[derive(Debug)]
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

    let stats = BenchStats::from_samples(&samples);

    if verbose {
        println!(
            "bench {} ... {} iterations, {:.2?} avg, {:.2?} median",
            bench.name, stats.iterations, stats.mean, stats.median
        );
    }

    BenchResult::Success(stats)
}

/// Run all benchmarks and return summary.
pub fn run_all_benchmarks(
    file: &SourceFile,
    filter: Option<&str>,
    iterations: usize,
    verbose: bool,
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

    let mut summary = BenchSummary::default();

    for bench in &filtered_benches {
        let result = run_benchmark(file, bench, iterations, verbose);

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

        let stats = BenchStats::from_samples(&samples);

        assert_eq!(stats.iterations, 5);
        assert_eq!(stats.min, Duration::from_micros(100));
        assert_eq!(stats.max, Duration::from_micros(150));
        assert_eq!(stats.median, Duration::from_micros(130));
    }
}
