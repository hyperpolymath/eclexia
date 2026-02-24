// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Tree-walking interpreter for Eclexia.
//!
//! This interpreter provides a simple execution model for Eclexia programs,
//! suitable for development, testing, and the REPL. It supports:
//!
//! - Basic expression evaluation
//! - Adaptive function solution selection
//! - Resource tracking (simulated)
//! - Shadow price computation (simplified)

mod builtins;
mod env;
mod error;
mod eval;
mod value;

pub use env::Environment;
pub use error::{RuntimeError, RuntimeResult};
pub use eval::Interpreter;
pub use value::Value;

use eclexia_ast::SourceFile;
use std::cell::RefCell;

thread_local! {
    static OUTPUT_CAPTURE: RefCell<Option<String>> = const { RefCell::new(None) };
}

fn begin_output_capture() {
    OUTPUT_CAPTURE.with(|slot| {
        *slot.borrow_mut() = Some(String::new());
    });
}

fn end_output_capture() -> String {
    OUTPUT_CAPTURE
        .with(|slot| slot.borrow_mut().take())
        .unwrap_or_default()
}

pub(crate) fn emit_output(chunk: &str) {
    OUTPUT_CAPTURE.with(|slot| {
        let mut capture = slot.borrow_mut();
        if let Some(buf) = capture.as_mut() {
            buf.push_str(chunk);
        } else {
            print!("{}", chunk);
        }
    });
}

/// Execute an Eclexia program and return the result.
pub fn run(file: &SourceFile) -> RuntimeResult<Value> {
    let mut interp = Interpreter::new();
    interp.run(file)
}

/// Execute an Eclexia program and capture `print`/`println` built-in output.
pub fn run_capturing_output(file: &SourceFile) -> RuntimeResult<(Value, String)> {
    begin_output_capture();
    let mut interp = Interpreter::new();
    let result = interp.run(file);
    let captured = end_output_capture();
    result.map(|value| (value, captured))
}

/// Execute an Eclexia program with custom resource constraints.
pub fn run_with_constraints(
    file: &SourceFile,
    energy_budget: f64,
    carbon_budget: f64,
) -> RuntimeResult<Value> {
    let mut interp = Interpreter::new();
    interp.set_energy_budget(energy_budget);
    interp.set_carbon_budget(carbon_budget);
    interp.run(file)
}
