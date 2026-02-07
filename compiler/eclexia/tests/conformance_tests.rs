// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Automated conformance test runner.
//!
//! Discovers and runs all tests in tests/conformance/{valid,invalid}/

use std::path::{Path, PathBuf};
use std::process::Command;

/// Run a valid test file (should succeed)
fn run_valid_test(path: &Path) -> Result<(), String> {
    let output = Command::new("cargo")
        .args(&["run", "--", "run", path.to_str().unwrap()])
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
    let output = Command::new("cargo")
        .args(&["run", "--", "run", path.to_str().unwrap()])
        .output()
        .map_err(|e| format!("Failed to execute: {}", e))?;

    if output.status.success() {
        return Err("Test succeeded (should fail)".to_string());
    }

    // Check that error mentions resources or constraints
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.contains("resource") && !stderr.contains("constraint") && !stderr.contains("violation") {
        return Err(format!(
            "Test failed but not with resource error:\n{}",
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
        let name = test_path.file_name().unwrap().to_str().unwrap();
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
    for test_path in &tests {
        let name = test_path.file_name().unwrap().to_str().unwrap();
        print!("Testing {}... ", name);

        match run_invalid_test(test_path) {
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
        panic!("{} invalid test(s) failed", failed.len());
    }

    println!("\n✓ All {} invalid conformance tests passed", tests.len());
}
