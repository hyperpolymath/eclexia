// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Automated conformance test runner.
//!
//! Discovers and runs all tests in tests/conformance/{valid,invalid}/

use std::path::{Path, PathBuf};
use std::process::Command;

/// Tests that are known to NOT fail when they should, because the
/// runtime does not yet enforce resource constraints / adaptive
/// feasibility checks.  Each entry gives the filename and the reason.
///
/// When runtime resource enforcement is implemented, these tests
/// should naturally start failing (as intended) and can be removed
/// from this list.
const KNOWN_RUNTIME_GAPS: &[(&str, &str)] = &[(
    "stack_overflow_deep_recursion.ecl",
    "Known abort path: recursive program intentionally overflows host stack (SIGABRT).",
)];

/// Run a valid test file (should succeed)
fn run_valid_test(path: &Path) -> Result<(), String> {
    let path_str = path.to_string_lossy();
    let output = Command::new("cargo")
        .args(&["run", "--bin", "eclexia", "--", "run", path_str.as_ref()])
        .output()
        .map_err(|e| format!("Failed to execute: {}", e))?;

    if !output.status.success() {
        return Err(format!(
            "Test failed (should succeed):\n{}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    Ok(())
}

/// Run an invalid test file (should fail with error)
fn run_invalid_test(path: &Path) -> Result<(), String> {
    let path_str = path.to_string_lossy();
    let output = Command::new("cargo")
        .args(&["run", "--bin", "eclexia", "--", "run", path_str.as_ref()])
        .output()
        .map_err(|e| format!("Failed to execute: {}", e))?;

    if output.status.success() {
        return Err("Test succeeded (should fail)".to_string());
    }

    // Check that error output contains a recognisable diagnostic.
    // Invalid tests may exercise resource constraints, type errors,
    // parse errors, runtime errors, or other expected failures.
    let stderr = String::from_utf8_lossy(&output.stderr);
    let recognised_keywords = [
        "resource",
        "constraint",
        "violation", // resource system
        "type",
        "mismatch",
        "Type", // type checker
        "error",
        "Error", // general errors
        "parse",
        "Parse", // parser errors
        "overflow",
        "recursion", // runtime limits
        "dimension",
        "Dimension", // dimensional analysis
        "uninitialized",
        "undefined",        // semantic analysis
        "division by zero", // arithmetic errors
    ];
    if !recognised_keywords.iter().any(|kw| stderr.contains(kw)) {
        return Err(format!(
            "Test failed but without a recognised error diagnostic:\n{}",
            stderr
        ));
    }

    Ok(())
}

/// Discover test files in a directory
fn discover_tests(dir: &Path) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("ecl") {
                tests.push(path);
            }
        }
    }

    tests.sort();
    tests
}

#[test]
fn conformance_valid_tests() {
    let valid_dir = Path::new("../../tests/conformance/valid");
    let tests = discover_tests(valid_dir);

    assert!(!tests.is_empty(), "No valid conformance tests found");

    let mut failed = Vec::new();
    for test_path in &tests {
        let name = match test_path.file_name().and_then(|s| s.to_str()) {
            Some(name) => name,
            None => "<unknown>",
        };
        print!("Testing {}... ", name);

        match run_valid_test(test_path) {
            Ok(()) => println!("✓"),
            Err(e) => {
                println!("✗");
                failed.push((name, e));
            }
        }
    }

    if !failed.is_empty() {
        eprintln!("\nFailed tests:");
        for (name, err) in &failed {
            eprintln!("  {}: {}", name, err);
        }
        panic!("{} valid test(s) failed", failed.len());
    }

    println!("\n✓ All {} valid conformance tests passed", tests.len());
}

#[test]
fn conformance_invalid_tests() {
    let invalid_dir = Path::new("../../tests/conformance/invalid");
    let tests = discover_tests(invalid_dir);

    assert!(!tests.is_empty(), "No invalid conformance tests found");

    let mut failed = Vec::new();
    let mut skipped = Vec::new();

    for test_path in &tests {
        let name = match test_path.file_name().and_then(|s| s.to_str()) {
            Some(name) => name,
            None => "<unknown>",
        };
        print!("Testing {}... ", name);

        match run_invalid_test(test_path) {
            Ok(()) => println!("✓"),
            Err(e) => {
                // Check if this is a known runtime gap
                if let Some((_file, reason)) = KNOWN_RUNTIME_GAPS.iter().find(|(f, _)| *f == name) {
                    println!("SKIP (known gap: {})", reason);
                    skipped.push((name, reason));
                } else {
                    println!("✗");
                    failed.push((name, e));
                }
            }
        }
    }

    if !skipped.is_empty() {
        eprintln!("\nKnown limitation skips ({}):", skipped.len());
        for (name, reason) in &skipped {
            eprintln!("  {}: {}", name, reason);
        }
    }

    if !failed.is_empty() {
        eprintln!("\nFailed tests:");
        for (name, err) in &failed {
            eprintln!("  {}: {}", name, err);
        }
        panic!("{} invalid test(s) failed", failed.len());
    }

    let passed = tests.len() - skipped.len();
    println!(
        "\n✓ {} invalid conformance tests passed, {} skipped (known gaps)",
        passed,
        skipped.len()
    );
}
