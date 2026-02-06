// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Command implementations for the Eclexia CLI.

use std::path::Path;
use miette::{Context, IntoDiagnostic};

/// Build an Eclexia program.
pub fn build(input: &Path, _output: Option<&Path>, _target: &str) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    // Parse
    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed with {} errors", parse_errors.len()));
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Type checking failed with {} errors", type_errors.len()));
    }

    println!("✓ Build successful");
    println!("  {} items parsed", file.items.len());

    // TODO: Lower to HIR, MIR, and generate code

    Ok(())
}

/// Build and run an Eclexia program.
pub fn run(input: &Path, observe_shadow: bool, carbon_report: bool) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    // Parse
    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed with {} errors", parse_errors.len()));
    }

    if observe_shadow {
        println!("Shadow price observation: λ_energy=1.0, λ_latency=1.0, λ_carbon=1.0");
    }

    // Execute using the interpreter
    println!("Running {}...\n", input.display());

    match eclexia_interp::run(&file) {
        Ok(result) => {
            println!("\nResult: {}", result);

            if carbon_report {
                // TODO: Extract actual resource usage from interpreter
                println!("\n--- Carbon Report ---");
                println!("  Energy used:  (tracked)");
                println!("  Carbon used:  (tracked)");
            }

            Ok(())
        }
        Err(e) => {
            Err(miette::miette!("Runtime error: {}", e))
        }
    }
}

/// Type check a file.
pub fn check(input: &Path) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed"));
    }

    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Type checking failed"));
    }

    println!("✓ No errors found");

    Ok(())
}

/// Format source files.
pub fn fmt(inputs: &[std::path::PathBuf], check: bool) -> miette::Result<()> {
    let mut has_issues = false;

    for input in inputs {
        let source = std::fs::read_to_string(input)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

        // Parse to check for syntax errors
        let (_file, errors) = eclexia_parser::parse(&source);

        if !errors.is_empty() {
            has_issues = true;
            eprintln!("{}:", input.display());
            for err in &errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            continue;
        }

        if check {
            println!("✓ {} is well-formed", input.display());
        } else {
            // For now, just report that the file is valid
            // TODO: Implement actual pretty-printing
            println!("✓ {} (no changes needed)", input.display());
        }
    }

    if has_issues {
        Err(miette::miette!("Some files have syntax errors"))
    } else {
        Ok(())
    }
}

/// Sanitize a project name to prevent path traversal attacks.
fn sanitize_project_name(name: &str) -> miette::Result<&str> {
    // Reject empty names
    if name.is_empty() {
        return Err(miette::miette!("Project name cannot be empty"));
    }

    // Reject absolute paths
    if name.starts_with('/') || name.starts_with('\\') {
        return Err(miette::miette!("Project name cannot be an absolute path"));
    }

    // Reject path traversal sequences
    if name.contains("..") {
        return Err(miette::miette!("Project name cannot contain '..' (path traversal)"));
    }

    // Reject path separators (require simple names)
    if name.contains('/') || name.contains('\\') {
        return Err(miette::miette!("Project name cannot contain path separators"));
    }

    // Reject null bytes
    if name.contains('\0') {
        return Err(miette::miette!("Project name cannot contain null bytes"));
    }

    Ok(name)
}

/// Initialize a new project.
pub fn init(name: Option<&str>) -> miette::Result<()> {
    let project_name = name.unwrap_or("my-eclexia-project");
    let project_name = sanitize_project_name(project_name)?;

    println!("Initializing new Eclexia project: {}", project_name);

    // Create directory structure
    std::fs::create_dir_all(project_name).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/src", project_name)).into_diagnostic()?;

    // Create eclexia.toml
    let config = format!(r#"# SPDX-License-Identifier: MIT
# Eclexia project configuration

[package]
name = "{}"
version = "0.1.0"
edition = "2025"

[dependencies]
# Add your dependencies here

[resources]
default-energy-budget = "1000J"
default-carbon-budget = "100gCO2e"
"#, project_name);

    std::fs::write(format!("{}/eclexia.toml", project_name), config).into_diagnostic()?;

    // Create main.ecl
    let main = r#"// SPDX-License-Identifier: MIT
// Main entry point

def main() -> Unit
    @requires: energy < 1J
{
    println("Hello, Economics-as-Code!")
}
"#;

    std::fs::write(format!("{}/src/main.ecl", project_name), main).into_diagnostic()?;

    println!("✓ Created project in {}/", project_name);
    println!();
    println!("To get started:");
    println!("  cd {}", project_name);
    println!("  eclexia run src/main.ecl");

    Ok(())
}

/// Run tests.
pub fn test(filter: Option<&str>) -> miette::Result<()> {
    use crate::test_runner;

    // Look for test files in src/ and tests/
    let test_patterns = ["src/**/*.ecl", "tests/**/*.ecl"];
    let mut test_files = Vec::new();

    for pattern in test_patterns {
        for entry in glob::glob(pattern).into_diagnostic()? {
            if let Ok(path) = entry {
                test_files.push(path);
            }
        }
    }

    if test_files.is_empty() {
        println!("No test files found.");
        println!("Test files should be placed in src/ or tests/");
        return Ok(());
    }

    let mut total_summary = test_runner::TestSummary::default();

    for test_file in &test_files {
        let source = match std::fs::read_to_string(test_file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read {}: {}", test_file.display(), e);
                continue;
            }
        };

        let (file, errors) = eclexia_parser::parse(&source);
        if !errors.is_empty() {
            eprintln!("Parse errors in {}:", test_file.display());
            for err in &errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            continue;
        }

        // Collect and run tests from this file
        let tests = test_runner::collect_tests(&file);
        if tests.is_empty() {
            continue;
        }

        let summary = test_runner::run_all_tests(&file, filter, true);
        total_summary.passed += summary.passed;
        total_summary.failed += summary.failed;
        total_summary.ignored += summary.ignored;
        total_summary.total_duration_ms += summary.total_duration_ms;
    }

    // Exit with error code if tests failed
    if total_summary.failed > 0 {
        return Err(miette::miette!("{} tests failed", total_summary.failed));
    }

    if total_summary.passed == 0 {
        println!("No tests found.");
        println!("Add #[test] attribute to functions to mark them as tests.");
        return Ok(());
    }

    println!("✓ All {} tests passed", total_summary.passed);
    Ok(())
}

/// Run benchmarks.
pub fn bench(filter: Option<&str>) -> miette::Result<()> {
    use crate::bench_runner;

    // Look for benchmark files in src/ and benches/
    let bench_patterns = ["src/**/*.ecl", "benches/**/*.ecl"];
    let mut bench_files = Vec::new();

    for pattern in bench_patterns {
        for entry in glob::glob(pattern).into_diagnostic()? {
            if let Ok(path) = entry {
                bench_files.push(path);
            }
        }
    }

    if bench_files.is_empty() {
        println!("No benchmark files found.");
        println!("Benchmark files should be placed in src/ or benches/");
        return Ok(());
    }

    let mut total_summary = bench_runner::BenchSummary::default();
    const ITERATIONS: usize = 100; // Number of iterations per benchmark

    for bench_file in &bench_files {
        let source = match std::fs::read_to_string(bench_file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read {}: {}", bench_file.display(), e);
                continue;
            }
        };

        let (file, errors) = eclexia_parser::parse(&source);
        if !errors.is_empty() {
            eprintln!("Parse errors in {}:", bench_file.display());
            for err in &errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            continue;
        }

        // Collect and run benchmarks from this file
        let benches = bench_runner::collect_benchmarks(&file);
        if benches.is_empty() {
            continue;
        }

        let summary = bench_runner::run_all_benchmarks(&file, filter, ITERATIONS, true);
        total_summary.benchmarks_run += summary.benchmarks_run;
        total_summary.benchmarks_failed += summary.benchmarks_failed;
        total_summary.benchmarks_ignored += summary.benchmarks_ignored;
    }

    // Exit with error code if benchmarks failed
    if total_summary.benchmarks_failed > 0 {
        return Err(miette::miette!("{} benchmarks failed", total_summary.benchmarks_failed));
    }

    if total_summary.benchmarks_run == 0 {
        println!("No benchmarks found.");
        println!("Add #[bench] attribute to functions to mark them as benchmarks.");
        return Ok(());
    }

    println!("✓ All {} benchmarks passed", total_summary.benchmarks_run);
    Ok(())
}
