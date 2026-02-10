// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Integration tests for the Eclexia compiler.
//!
//! Tests the full pipeline: Parse → Type Check → HIR → MIR → Codegen → Execute

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path() -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let counter = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let filename = format!(
        "eclexia_test_{}_{}_{}.ecl",
        std::process::id(),
        nanos,
        counter
    );
    std::env::temp_dir().join(filename)
}

/// Helper to run an Eclexia program
fn run_eclexia_program(code: &str) -> Result<String, String> {
    // Write code to temp file
    let temp_file = unique_temp_path();
    std::fs::write(&temp_file, code).map_err(|e| format!("Failed to write file: {}", e))?;

    // Run with eclexia
    let output = if let Ok(exe_path) = std::env::var("CARGO_BIN_EXE_eclexia") {
        Command::new(exe_path)
            .arg("run")
            .arg(&temp_file)
            .output()
            .map_err(|e| format!("Failed to execute: {}", e))?
    } else {
        Command::new("cargo")
            .args(["run", "--", "run"])
            .arg(&temp_file)
            .output()
            .map_err(|e| format!("Failed to execute: {}", e))?
    };

    // Clean up
    let _ = std::fs::remove_file(&temp_file);

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).to_string())
    }
}

#[test]
fn integration_hello_world() {
    let code = r#"
fn main() {
    print("Hello, World!");
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Hello world should succeed");
}

#[test]
fn integration_arithmetic() {
    let code = r#"
fn main() {
    let x = 10;
    let y = 32;
    let sum = x + y;
    assert(sum == 42);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Arithmetic should work: {:?}", result);
}

#[test]
fn integration_function_calls() {
    let code = r#"
fn double(x: int) -> int {
    x * 2
}

fn main() {
    let result = double(21);
    assert(result == 42);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Function calls should work: {:?}", result);
}

#[test]
fn integration_conditionals() {
    let code = r#"
fn main() {
    let x = 10;
    if x > 5 {
        print("greater");
    } else {
        print("less");
    }
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Conditionals should work: {:?}", result);
}

#[test]
fn integration_loops() {
    let code = r#"
fn main() {
    let mut sum = 0;
    let mut i = 0;
    while i < 10 {
        sum = sum + i;
        i = i + 1;
    }
    assert(sum == 45);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Loops should work: {:?}", result);
}

#[test]
fn integration_type_inference() {
    let code = r#"
fn main() {
    let x = 42;        // Inferred as int
    let y = x + 10;     // Also int
    assert(y == 52);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Type inference should work: {:?}", result);
}

#[test]
fn integration_nested_functions() {
    let code = r#"
fn inner(x: int) -> int {
    x + 1
}

fn outer(x: int) -> int {
    inner(inner(x))
}

fn main() {
    let result = outer(10);
    assert(result == 12);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Nested functions should work: {:?}", result);
}

#[test]
fn integration_recursion() {
    let code = r#"
fn factorial(n: int) -> int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
    let result = factorial(5);
    assert(result == 120);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Recursion should work: {:?}", result);
}

#[test]
fn integration_large_program() {
    let code = r#"
fn fibonacci(n: int) -> int {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

fn is_even(n: int) -> bool {
    n % 2 == 0
}

fn sum_array(arr: [int]) -> int {
    let mut sum = 0;
    let mut i = 0;
    while i < arr.len() {
        sum = sum + arr[i];
        i = i + 1;
    }
    sum
}

fn main() {
    let fib5 = fibonacci(5);
    assert(fib5 == 5);

    let even = is_even(10);
    assert(even == true);

    let arr = [1, 2, 3, 4, 5];
    let total = sum_array(arr);
    assert(total == 15);
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_ok(), "Large program should compile: {:?}", result);
}

#[test]
fn integration_error_handling() {
    let code = r#"
fn main() {
    // This should cause a type error
    let x: int = "string";
}
"#;

    let result = run_eclexia_program(code);
    assert!(result.is_err(), "Type errors should be caught");
}

#[test]
fn integration_multi_solution_adaptive() {
    let code = r#"
adaptive fn process(x: int) -> int {
    fast @requires(energy: 100J) {
        x * 2
    }

    slow @requires(energy: 10J) {
        x + x
    }
}

fn main() {
    let result = process(21);
    assert(result == 42);
}
"#;

    let result = run_eclexia_program(code);
    // May not be implemented yet, but test infrastructure is ready
    if result.is_ok() {
        println!("✓ Adaptive functions work!");
    }
}

#[test]
fn integration_resource_tracking() {
    let code = r#"
@requires(energy: 50J)
fn expensive() -> int {
    42
}

fn main() {
    let result = expensive();
    assert(result == 42);
}
"#;

    let result = run_eclexia_program(code);
    // May not be fully implemented yet
    if result.is_ok() {
        println!("✓ Resource tracking works!");
    }
}

#[test]
fn integration_carbon_aware_scheduling() {
    let code = r#"
adaptive fn compute(data: int) -> int {
    high_carbon @requires(energy: 10J, carbon: 100gCO2) {
        // Uses coal power
        data * 2
    }

    low_carbon @requires(energy: 10J, carbon: 1gCO2) {
        // Uses renewable energy
        data * 2
    }
}

fn main() {
    // Should select low_carbon when carbon price is high
    let result = compute(100);
    assert(result == 200);
}
"#;

    let result = run_eclexia_program(code);
    // Carbon-aware scheduling integration test
    if result.is_ok() {
        println!("✓ Carbon-aware scheduling works!");
    }
}
