// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type checking errors.

use eclexia_ast::span::Span;
use eclexia_ast::types::{Ty, TypeVar};
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
        hint: Option<String>,
    },

    #[error("undefined variable: {name}")]
    Undefined {
        span: Span,
        name: String,
        hint: Option<String>,
    },

    #[error("dimension mismatch: cannot combine {dim1} with {dim2}")]
    DimensionMismatch {
        span: Span,
        dim1: String,
        dim2: String,
        hint: Option<String>,
    },

    #[error("resource constraint violated: {message}")]
    ResourceViolation {
        span: Span,
        message: String,
        hint: Option<String>,
    },

    #[error("occurs check failed: infinite type")]
    OccursCheck {
        span: Span,
        hint: Option<String>,
    },

    #[error("infinite type: type variable {var:?} occurs in {ty}")]
    InfiniteType {
        span: Span,
        var: TypeVar,
        ty: Ty,
        hint: Option<String>,
    },

    #[error("{message}")]
    Custom {
        span: Span,
        message: String,
        hint: Option<String>,
    },
}

impl TypeError {
    /// Create an undefined variable error with suggestions.
    pub fn undefined_with_suggestions(
        span: Span,
        name: String,
        available_names: &[&str],
    ) -> Self {
        let hint = find_closest_match(&name, available_names)
            .map(|suggestion| format!("did you mean '{}'?", suggestion));

        Self::Undefined { span, name, hint }
    }

    /// Create a type mismatch error with hint.
    pub fn mismatch_with_hint(span: Span, expected: Ty, found: Ty, hint: String) -> Self {
        Self::Mismatch {
            span,
            expected,
            found,
            hint: Some(hint),
        }
    }

    /// Get the span of this error.
    pub fn span(&self) -> Span {
        match self {
            TypeError::Mismatch { span, .. } => *span,
            TypeError::Undefined { span, .. } => *span,
            TypeError::DimensionMismatch { span, .. } => *span,
            TypeError::ResourceViolation { span, .. } => *span,
            TypeError::OccursCheck { span, .. } => *span,
            TypeError::InfiniteType { span, .. } => *span,
            TypeError::Custom { span, .. } => *span,
        }
    }

    /// Get the hint for this error, if any.
    pub fn hint(&self) -> Option<&str> {
        match self {
            TypeError::Mismatch { hint, .. } => hint.as_deref(),
            TypeError::Undefined { hint, .. } => hint.as_deref(),
            TypeError::DimensionMismatch { hint, .. } => hint.as_deref(),
            TypeError::ResourceViolation { hint, .. } => hint.as_deref(),
            TypeError::OccursCheck { hint, .. } => hint.as_deref(),
            TypeError::InfiniteType { hint, .. } => hint.as_deref(),
            TypeError::Custom { hint, .. } => hint.as_deref(),
        }
    }

    /// Format this error with line:column information from source.
    pub fn format_with_source(&self, source: &str) -> String {
        let span = self.span();
        let location = span.format_location(source);
        let mut output = format!("{}: {}", location, self);

        if let Some(hint) = self.hint() {
            output.push_str(&format!("\n  hint: {}", hint));
        }

        output
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
