// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Test runner for Eclexia programs.

use eclexia_ast::{Attribute, Function, Item, SourceFile};
use eclexia_codegen::{Backend, BytecodeGenerator, VirtualMachine, VmValue};
use std::time::Instant;

/// A test function with metadata.
#[derive(Debug)]
pub struct TestFunction {
    pub name: String,
    pub attributes: Vec<Attribute>,
}

/// Test result.
#[derive(Debug)]
pub enum TestResult {
    Passed { duration_ms: f64 },
    Failed { error: String, duration_ms: f64 },
    Ignored,
}

/// Test summary statistics.
#[derive(Debug, Default)]
pub struct TestSummary {
    pub passed: usize,
    pub failed: usize,
    pub ignored: usize,
    pub total_duration_ms: f64,
}

/// Collect all test functions from a source file.
pub fn collect_tests(file: &SourceFile) -> Vec<TestFunction> {
    let mut tests = Vec::new();

    for item in &file.items {
        if let Item::Function(func) = item {
            if has_test_attribute(&func.attributes) {
                tests.push(TestFunction {
                    name: func.name.to_string(),
                    attributes: func.attributes.clone(),
                });
            }
        }
    }

    tests
}

/// Check if attributes contain #[test]
fn has_test_attribute(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attr| attr.name == "test")
}

/// Check if attributes contain #[ignore]
fn has_ignore_attribute(attributes: &[Attribute]) -> bool {
    attributes.iter().any(|attr| attr.name == "ignore")
}

/// Run a single test function.
pub fn run_test(
    file: &SourceFile,
    test: &TestFunction,
    verbose: bool,
) -> TestResult {
    if has_ignore_attribute(&test.attributes) {
        if verbose {
            println!("test {} ... ignored", test.name);
        }
        return TestResult::Ignored;
    }

    let start = Instant::now();

    // Type check
    let type_errors = eclexia_typeck::check(file);
    if !type_errors.is_empty() {
        let duration = start.elapsed().as_secs_f64() * 1000.0;
        return TestResult::Failed {
            error: format!("Type checking failed: {:?}", type_errors),
            duration_ms: duration,
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
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            return TestResult::Failed {
                error: format!("Codegen failed: {}", e),
                duration_ms: duration,
            };
        }
    };

    // Find the test function in the bytecode
    let test_fn_index = bytecode.functions.iter().position(|f| f.name == test.name);

    if test_fn_index.is_none() {
        let duration = start.elapsed().as_secs_f64() * 1000.0;
        return TestResult::Failed {
            error: format!("Test function '{}' not found in bytecode", test.name),
            duration_ms: duration,
        };
    }

    // Execute the test function
    let mut vm = VirtualMachine::new(bytecode);
    match vm.run() {
        Ok(VmValue::Unit) | Ok(VmValue::Bool(true)) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            if verbose {
                println!("test {} ... ok ({:.2}ms)", test.name, duration);
            }
            TestResult::Passed { duration_ms: duration }
        }
        Ok(VmValue::Bool(false)) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            if verbose {
                println!("test {} ... FAILED (assertion failed)", test.name);
            }
            TestResult::Failed {
                error: "assertion failed".to_string(),
                duration_ms: duration,
            }
        }
        Ok(other) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            if verbose {
                println!("test {} ... FAILED (unexpected return value)", test.name);
            }
            TestResult::Failed {
                error: format!("Expected Unit or Bool, got {:?}", other),
                duration_ms: duration,
            }
        }
        Err(e) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            if verbose {
                println!("test {} ... FAILED ({})", test.name, e);
            }
            TestResult::Failed {
                error: e.to_string(),
                duration_ms: duration,
            }
        }
    }
}

/// Run all tests and return summary.
pub fn run_all_tests(
    file: &SourceFile,
    filter: Option<&str>,
    verbose: bool,
) -> TestSummary {
    let tests = collect_tests(file);

    let filtered_tests: Vec<_> = if let Some(pattern) = filter {
        tests
            .into_iter()
            .filter(|t| t.name.contains(pattern))
            .collect()
    } else {
        tests
    };

    if filtered_tests.is_empty() {
        println!("No tests found");
        return TestSummary::default();
    }

    println!("\nrunning {} tests", filtered_tests.len());

    let mut summary = TestSummary::default();

    for test in &filtered_tests {
        let result = run_test(file, test, verbose);

        match result {
            TestResult::Passed { duration_ms } => {
                summary.passed += 1;
                summary.total_duration_ms += duration_ms;
            }
            TestResult::Failed { duration_ms, .. } => {
                summary.failed += 1;
                summary.total_duration_ms += duration_ms;
            }
            TestResult::Ignored => {
                summary.ignored += 1;
            }
        }
    }

    // Print summary
    println!("\ntest result: {}. {} passed; {} failed; {} ignored; finished in {:.2}s\n",
        if summary.failed == 0 { "ok" } else { "FAILED" },
        summary.passed,
        summary.failed,
        summary.ignored,
        summary.total_duration_ms / 1000.0
    );

    summary
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_test_attribute() {
        use eclexia_ast::span::Span;
        use smol_str::SmolStr;

        let attrs = vec![Attribute {
            span: Span::new(0, 0),
            name: SmolStr::new("test"),
            args: vec![],
        }];

        assert!(has_test_attribute(&attrs));
    }

    #[test]
    fn test_has_ignore_attribute() {
        use eclexia_ast::span::Span;
        use smol_str::SmolStr;

        let attrs = vec![Attribute {
            span: Span::new(0, 0),
            name: SmolStr::new("ignore"),
            args: vec![],
        }];

        assert!(has_ignore_attribute(&attrs));
    }
}
