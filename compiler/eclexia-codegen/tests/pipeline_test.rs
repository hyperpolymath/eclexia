// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! End-to-end integration tests for the complete compiler pipeline.
//!
//! Tests: Source → Lexer → Parser → AST → TypeChecker → HIR → MIR → Bytecode → VM

use eclexia_parser::Parser;
use eclexia_typeck;
use eclexia_hir;
use eclexia_mir;
use eclexia_codegen::{Backend, BytecodeGenerator, VirtualMachine};

/// Helper to run the full pipeline
fn compile_and_run(source: &str) -> Result<eclexia_codegen::VmValue, String> {
    // 1. Parse (lexer is internal to parser)
    let mut parser = Parser::new(source);
    let (ast, parse_errors) = parser.parse_file();
    if !parse_errors.is_empty() {
        return Err(format!("Parse errors: {:?}", parse_errors));
    }

    // 2. Type check
    let errors = eclexia_typeck::check(&ast);
    if !errors.is_empty() {
        return Err(format!("Type errors: {:?}", errors));
    }

    // 3. Lower to HIR
    let hir = eclexia_hir::lower_source_file(&ast);

    // 5. Lower to MIR
    let mir = eclexia_mir::lower_hir_file(&hir);

    // 6. Generate bytecode
    let mut codegen = BytecodeGenerator::new();
    let bytecode = codegen.generate(&mir)
        .map_err(|e| format!("Codegen error: {}", e))?;

    // 7. Execute on VM
    let mut vm = VirtualMachine::new(bytecode);
    vm.run().map_err(|e| format!("VM error: {}", e))
}

#[test]
fn test_simple_arithmetic() {
    let source = r#"
        fn main() -> Int {
            let a = 10
            let b = 20
            a + b
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 30),
        Ok(other) => panic!("Expected Int(30), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_function_call() {
    let source = r#"
        fn add(x: Int, y: Int) -> Int {
            x + y
        }

        fn main() -> Int {
            add(15, 25)
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 40),
        Ok(other) => panic!("Expected Int(40), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_conditional() {
    let source = r#"
        fn main() -> Int {
            let x = 10
            if x > 5 {
                100
            } else {
                200
            }
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 100),
        Ok(other) => panic!("Expected Int(100), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_factorial() {
    let source = r#"
        fn factorial(n: Int) -> Int {
            if n <= 1 {
                1
            } else {
                n * factorial(n - 1)
            }
        }

        fn main() -> Int {
            factorial(5)
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 120), // 5! = 120
        Ok(other) => panic!("Expected Int(120), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_type_inference() {
    let source = r#"
        fn identity(x) {
            x
        }

        fn main() -> Int {
            identity(42)
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 42),
        Ok(other) => panic!("Expected Int(42), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_boolean_logic() {
    let source = r#"
        fn main() -> Bool {
            let a = true
            let b = false
            a && !b
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Bool(b)) => assert!(b),
        Ok(other) => panic!("Expected Bool(true), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_comparison_chain() {
    let source = r#"
        fn main() -> Bool {
            let x = 10;
            let y = 20;
            let z = 30;
            (x < y) && (y < z)
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Bool(b)) => assert!(b),
        Ok(other) => panic!("Expected Bool(true), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_nested_function_calls() {
    let source = r#"
        fn double(x: Int) -> Int {
            x * 2
        }

        fn triple(x: Int) -> Int {
            x * 3
        }

        fn main() -> Int {
            double(triple(5))
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Int(n)) => assert_eq!(n, 30), // 5 * 3 * 2 = 30
        Ok(other) => panic!("Expected Int(30), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}

#[test]
fn test_float_arithmetic() {
    let source = r#"
        fn main() -> Float {
            let x = 10.5
            let y = 2.0
            x * y
        }
    "#;

    match compile_and_run(source) {
        Ok(eclexia_codegen::VmValue::Float(f)) => assert!((f - 21.0).abs() < 0.001),
        Ok(other) => panic!("Expected Float(21.0), got {:?}", other),
        Err(e) => panic!("Pipeline failed: {}", e),
    }
}
