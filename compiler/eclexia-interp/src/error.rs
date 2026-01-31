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
    UndefinedVariable {
        name: String,
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("type error: expected {expected}, got {got}")]
    TypeError {
        expected: String,
        got: String,
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("arity mismatch: expected {expected} arguments, got {got}")]
    ArityMismatch {
        expected: usize,
        got: usize,
        hint: Option<String>,
    },

    #[error("division by zero")]
    DivisionByZero {
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("index out of bounds: {index} >= {len}")]
    IndexOutOfBounds {
        index: usize,
        len: usize,
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("no field '{field}' on struct '{struct_name}'")]
    NoSuchField {
        struct_name: String,
        field: String,
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("cannot call non-function value of type {ty}")]
    NotCallable {
        ty: String,
        span: Option<Span>,
        hint: Option<String>,
    },

    #[error("resource constraint violated: {message}")]
    ResourceViolation {
        message: String,
        hint: Option<String>,
    },

    #[error("no suitable solution found for adaptive function '{name}'")]
    NoSuitableSolution {
        name: String,
        hint: Option<String>,
    },

    #[error("return from top level")]
    Return(crate::Value),

    #[error("break outside loop")]
    Break,

    #[error("continue outside loop")]
    Continue,

    #[error("{message}")]
    Custom {
        message: String,
        span: Option<Span>,
        hint: Option<String>,
    },
}

impl RuntimeError {
    pub fn type_error(expected: impl Into<String>, got: impl Into<String>) -> Self {
        let expected_str = expected.into();
        let got_str = got.into();
        let hint = Some(format!(
            "check that the value's type matches what is expected in this context"
        ));
        Self::TypeError {
            expected: expected_str,
            got: got_str,
            span: None,
            hint,
        }
    }

    pub fn undefined(name: impl Into<String>) -> Self {
        Self::UndefinedVariable {
            name: name.into(),
            span: None,
            hint: Some("check that the variable is defined before use".to_string()),
        }
    }

    pub fn undefined_with_suggestions(
        name: impl Into<String>,
        available_names: &[&str],
    ) -> Self {
        let name_str = name.into();
        let hint = find_closest_match(&name_str, available_names)
            .map(|suggestion| format!("did you mean '{}'?", suggestion))
            .or_else(|| Some("check that the variable is defined before use".to_string()));

        Self::UndefinedVariable {
            name: name_str,
            span: None,
            hint,
        }
    }

    pub fn no_such_field_with_suggestions(
        struct_name: impl Into<String>,
        field: impl Into<String>,
        available_fields: &[&str],
    ) -> Self {
        let field_str = field.into();
        let hint = find_closest_match(&field_str, available_fields)
            .map(|suggestion| format!("did you mean '{}'?", suggestion))
            .or_else(|| Some(format!("available fields: {}", available_fields.join(", "))));

        Self::NoSuchField {
            struct_name: struct_name.into(),
            field: field_str,
            span: None,
            hint,
        }
    }

    pub fn custom(message: impl Into<String>) -> Self {
        Self::Custom {
            message: message.into(),
            span: None,
            hint: None,
        }
    }

    pub fn custom_with_hint(message: impl Into<String>, hint: impl Into<String>) -> Self {
        Self::Custom {
            message: message.into(),
            span: None,
            hint: Some(hint.into()),
        }
    }

    /// Get the span of this error if available.
    pub fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVariable { span, .. } => *span,
            Self::TypeError { span, .. } => *span,
            Self::ArityMismatch { .. } => None,
            Self::DivisionByZero { span, .. } => *span,
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

    /// Get the hint for this error, if any.
    pub fn hint(&self) -> Option<&str> {
        match self {
            Self::UndefinedVariable { hint, .. } => hint.as_deref(),
            Self::TypeError { hint, .. } => hint.as_deref(),
            Self::ArityMismatch { hint, .. } => hint.as_deref(),
            Self::DivisionByZero { hint, .. } => hint.as_deref(),
            Self::IndexOutOfBounds { hint, .. } => hint.as_deref(),
            Self::NoSuchField { hint, .. } => hint.as_deref(),
            Self::NotCallable { hint, .. } => hint.as_deref(),
            Self::ResourceViolation { hint, .. } => hint.as_deref(),
            Self::NoSuitableSolution { hint, .. } => hint.as_deref(),
            Self::Return(_) => None,
            Self::Break => None,
            Self::Continue => None,
            Self::Custom { hint, .. } => hint.as_deref(),
        }
    }

    /// Format this error with line:column information from source.
    pub fn format_with_source(&self, source: &str) -> String {
        let mut output = if let Some(span) = self.span() {
            let location = span.format_location(source);
            format!("{}: {}", location, self)
        } else {
            self.to_string()
        };

        if let Some(hint) = self.hint() {
            output.push_str(&format!("\n  hint: {}", hint));
        }

        output
    }

    /// Add span information to this error.
    pub fn with_span(self, span: Span) -> Self {
        match self {
            Self::UndefinedVariable { name, hint, .. } => {
                Self::UndefinedVariable { name, span: Some(span), hint }
            }
            Self::TypeError { expected, got, hint, .. } => {
                Self::TypeError { expected, got, span: Some(span), hint }
            }
            Self::ArityMismatch { expected, got, hint } => Self::ArityMismatch { expected, got, hint },
            Self::DivisionByZero { hint, .. } => Self::DivisionByZero { span: Some(span), hint },
            Self::IndexOutOfBounds { index, len, hint, .. } => {
                Self::IndexOutOfBounds { index, len, span: Some(span), hint }
            }
            Self::NoSuchField { struct_name, field, hint, .. } => {
                Self::NoSuchField { struct_name, field, span: Some(span), hint }
            }
            Self::NotCallable { ty, hint, .. } => Self::NotCallable { ty, span: Some(span), hint },
            Self::ResourceViolation { message, hint } => Self::ResourceViolation { message, hint },
            Self::NoSuitableSolution { name, hint } => Self::NoSuitableSolution { name, hint },
            Self::Return(v) => Self::Return(v),
            Self::Break => Self::Break,
            Self::Continue => Self::Continue,
            Self::Custom { message, hint, .. } => Self::Custom { message, span: Some(span), hint },
        }
    }
}

/// Calculate Levenshtein distance between two strings.
fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let a_len = a_chars.len();
    let b_len = b_chars.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    let mut prev_row: Vec<usize> = (0..=b_len).collect();
    let mut curr_row = vec![0; b_len + 1];

    for (i, a_char) in a_chars.iter().enumerate() {
        curr_row[0] = i + 1;

        for (j, b_char) in b_chars.iter().enumerate() {
            let cost = if a_char == b_char { 0 } else { 1 };
            curr_row[j + 1] = (curr_row[j] + 1)
                .min(prev_row[j + 1] + 1)
                .min(prev_row[j] + cost);
        }

        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[b_len]
}

/// Find the closest matching name from available names.
fn find_closest_match<'a>(target: &str, available: &[&'a str]) -> Option<&'a str> {
    if available.is_empty() {
        return None;
    }

    let mut best_match = available[0];
    let mut best_distance = levenshtein_distance(target, available[0]);

    for &candidate in &available[1..] {
        let distance = levenshtein_distance(target, candidate);
        if distance < best_distance {
            best_distance = distance;
            best_match = candidate;
        }
    }

    // Only suggest if distance is reasonable (within 3 edits for short names, proportional for longer)
    let max_distance = (target.len() / 3).max(3);
    if best_distance <= max_distance {
        Some(best_match)
    } else {
        None
    }
}
