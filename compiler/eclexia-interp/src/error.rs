// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime errors for the interpreter.

use eclexia_ast::span::Span;
use thiserror::Error;

/// Result type for runtime operations.
pub type RuntimeResult<T> = Result<T, RuntimeError>;

/// A runtime error.
#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("undefined variable: {name}")]
    UndefinedVariable { name: String, span: Option<Span> },

    #[error("type error: expected {expected}, got {got}")]
    TypeError { expected: String, got: String, span: Option<Span> },

    #[error("arity mismatch: expected {expected} arguments, got {got}")]
    ArityMismatch { expected: usize, got: usize },

    #[error("division by zero")]
    DivisionByZero { span: Option<Span> },

    #[error("index out of bounds: {index} >= {len}")]
    IndexOutOfBounds { index: usize, len: usize, span: Option<Span> },

    #[error("no field '{field}' on struct '{struct_name}'")]
    NoSuchField { struct_name: String, field: String, span: Option<Span> },

    #[error("cannot call non-function value of type {ty}")]
    NotCallable { ty: String, span: Option<Span> },

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
    Custom { message: String, span: Option<Span> },
}

impl RuntimeError {
    pub fn type_error(expected: impl Into<String>, got: impl Into<String>) -> Self {
        Self::TypeError {
            expected: expected.into(),
            got: got.into(),
            span: None,
        }
    }

    pub fn undefined(name: impl Into<String>) -> Self {
        Self::UndefinedVariable { name: name.into(), span: None }
    }

    pub fn custom(message: impl Into<String>) -> Self {
        Self::Custom {
            message: message.into(),
            span: None,
        }
    }

    /// Get the span of this error if available.
    pub fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVariable { span, .. } => *span,
            Self::TypeError { span, .. } => *span,
            Self::ArityMismatch { .. } => None,
            Self::DivisionByZero { span } => *span,
            Self::IndexOutOfBounds { span, .. } => *span,
            Self::NoSuchField { span, .. } => *span,
            Self::NotCallable { span, .. } => *span,
            Self::ResourceViolation { .. } => None,
            Self::NoSuitableSolution { .. } => None,
            Self::Return(_) => None,
            Self::Break => None,
            Self::Continue => None,
            Self::Custom { span, .. } => *span,
        }
    }

    /// Format this error with line:column information from source.
    pub fn format_with_source(&self, source: &str) -> String {
        if let Some(span) = self.span() {
            let location = span.format_location(source);
            format!("{}: {}", location, self)
        } else {
            self.to_string()
        }
    }

    /// Add span information to this error.
    pub fn with_span(self, span: Span) -> Self {
        match self {
            Self::UndefinedVariable { name, .. } => Self::UndefinedVariable { name, span: Some(span) },
            Self::TypeError { expected, got, .. } => Self::TypeError { expected, got, span: Some(span) },
            Self::ArityMismatch { expected, got } => Self::ArityMismatch { expected, got },
            Self::DivisionByZero { .. } => Self::DivisionByZero { span: Some(span) },
            Self::IndexOutOfBounds { index, len, .. } => Self::IndexOutOfBounds { index, len, span: Some(span) },
            Self::NoSuchField { struct_name, field, .. } => Self::NoSuchField { struct_name, field, span: Some(span) },
            Self::NotCallable { ty, .. } => Self::NotCallable { ty, span: Some(span) },
            Self::ResourceViolation { message } => Self::ResourceViolation { message },
            Self::NoSuitableSolution { name } => Self::NoSuitableSolution { name },
            Self::Return(v) => Self::Return(v),
            Self::Break => Self::Break,
            Self::Continue => Self::Continue,
            Self::Custom { message, .. } => Self::Custom { message, span: Some(span) },
        }
    }
}
