// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type checking errors.

use eclexia_ast::span::Span;
use eclexia_ast::types::Ty;
use thiserror::Error;

/// Result type for type checking operations.
pub type TypeResult<T> = Result<T, TypeError>;

/// A type checking error.
#[derive(Debug, Error)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    Mismatch {
        span: Span,
        expected: Ty,
        found: Ty,
    },

    #[error("undefined variable: {name}")]
    Undefined {
        span: Span,
        name: String,
    },

    #[error("dimension mismatch: cannot combine {dim1} with {dim2}")]
    DimensionMismatch {
        span: Span,
        dim1: String,
        dim2: String,
    },

    #[error("resource constraint violated: {message}")]
    ResourceViolation {
        span: Span,
        message: String,
    },

    #[error("occurs check failed: infinite type")]
    OccursCheck {
        span: Span,
    },

    #[error("{message}")]
    Custom {
        span: Span,
        message: String,
    },
}

impl TypeError {
    /// Get the span of this error.
    pub fn span(&self) -> Span {
        match self {
            TypeError::Mismatch { span, .. } => *span,
            TypeError::Undefined { span, .. } => *span,
            TypeError::DimensionMismatch { span, .. } => *span,
            TypeError::ResourceViolation { span, .. } => *span,
            TypeError::OccursCheck { span } => *span,
            TypeError::Custom { span, .. } => *span,
        }
    }

    /// Format this error with line:column information from source.
    pub fn format_with_source(&self, source: &str) -> String {
        let span = self.span();
        let location = span.format_location(source);
        format!("{}: {}", location, self)
    }
}
