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
            eprintln!("  {}", err);
        }
        return Err(miette::miette!("Parsing failed with {} errors", parse_errors.len()));
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err);
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
    build(input, None, "native")?;

    if observe_shadow {
        println!("Shadow price observation enabled (not yet implemented)");
    }

    if carbon_report {
        println!("Carbon reporting enabled (not yet implemented)");
    }

    // TODO: Execute the compiled program

    Ok(())
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
            eprintln!("  {}", err);
        }
        return Err(miette::miette!("Parsing failed"));
    }

    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err);
        }
        return Err(miette::miette!("Type checking failed"));
    }

    println!("✓ No errors found");

    Ok(())
}

/// Format source files.
pub fn fmt(inputs: &[std::path::PathBuf], check: bool) -> miette::Result<()> {
    for input in inputs {
        if check {
            println!("Checking {}...", input.display());
        } else {
            println!("Formatting {}...", input.display());
        }
        // TODO: Implement formatter
    }

    Ok(())
}

/// Initialize a new project.
pub fn init(name: Option<&str>) -> miette::Result<()> {
    let project_name = name.unwrap_or("my-eclexia-project");

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
pub fn test(_filter: Option<&str>) -> miette::Result<()> {
    println!("Running tests...");
    // TODO: Implement test runner
    Ok(())
}

/// Run benchmarks.
pub fn bench(_filter: Option<&str>) -> miette::Result<()> {
    println!("Running benchmarks...");
    // TODO: Implement benchmark runner
    Ok(())
}
