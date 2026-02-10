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

/// Execute an Eclexia program and return the result.
pub fn run(file: &SourceFile) -> RuntimeResult<Value> {
    let mut interp = Interpreter::new();
    interp.run(file)
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
