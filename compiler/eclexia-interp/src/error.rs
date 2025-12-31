// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime errors for the interpreter.

use thiserror::Error;

/// Result type for runtime operations.
pub type RuntimeResult<T> = Result<T, RuntimeError>;

/// A runtime error.
#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("undefined variable: {name}")]
    UndefinedVariable { name: String },

    #[error("type error: expected {expected}, got {got}")]
    TypeError { expected: String, got: String },

    #[error("arity mismatch: expected {expected} arguments, got {got}")]
    ArityMismatch { expected: usize, got: usize },

    #[error("division by zero")]
    DivisionByZero,

    #[error("index out of bounds: {index} >= {len}")]
    IndexOutOfBounds { index: usize, len: usize },

    #[error("no field '{field}' on struct '{struct_name}'")]
    NoSuchField { struct_name: String, field: String },

    #[error("cannot call non-function value of type {ty}")]
    NotCallable { ty: String },

    #[error("resource constraint violated: {message}")]
    ResourceViolation { message: String },

    #[error("no suitable solution found for adaptive function '{name}'")]
    NoSuitableSolution { name: String },

    #[error("return from top level")]
    Return(crate::Value),

    #[error("break outside loop")]
    Break,

    #[error("continue outside loop")]
    Continue,

    #[error("{message}")]
    Custom { message: String },
}

impl RuntimeError {
    pub fn type_error(expected: impl Into<String>, got: impl Into<String>) -> Self {
        Self::TypeError {
            expected: expected.into(),
            got: got.into(),
        }
    }

    pub fn undefined(name: impl Into<String>) -> Self {
        Self::UndefinedVariable { name: name.into() }
    }

    pub fn custom(message: impl Into<String>) -> Self {
        Self::Custom {
            message: message.into(),
        }
    }
}
