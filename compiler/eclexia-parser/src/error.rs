// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Parser error types.

use eclexia_ast::span::Span;
use eclexia_lexer::{Token, TokenKind};
use thiserror::Error;

/// Result type for parsing operations.
pub type ParseResult<T> = Result<T, ParseError>;

/// A parsing error.
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("unexpected token {found:?}, expected {expected}")]
    UnexpectedToken {
        span: Span,
        found: TokenKind,
        expected: String,
        hint: Option<String>,
    },

    #[error("expected {expected:?}, found {found:?}")]
    ExpectedToken {
        span: Span,
        expected: TokenKind,
        found: TokenKind,
        hint: Option<String>,
    },

    #[error("expected identifier")]
    ExpectedIdentifier {
        span: Span,
        hint: Option<String>,
    },

    #[error("unexpected end of file")]
    UnexpectedEof {
        span: Span,
        hint: Option<String>,
    },

    #[error("invalid resource literal")]
    InvalidResourceLiteral {
        span: Span,
        hint: Option<String>,
    },

    #[error("{message}")]
    Custom {
        span: Span,
        message: String,
        hint: Option<String>,
    },
}

impl ParseError {
    /// Create an unexpected token error.
    pub fn unexpected_token(token: Token, expected: &str) -> Self {
        let hint = generate_unexpected_token_hint(&token.kind, expected);
        Self::UnexpectedToken {
            span: token.span,
            found: token.kind,
            expected: expected.to_string(),
            hint,
        }
    }

    /// Create an expected token error.
    pub fn expected_token(expected: TokenKind, found: Token) -> Self {
        let hint = generate_expected_token_hint(&expected, &found.kind);
        Self::ExpectedToken {
            span: found.span,
            expected,
            found: found.kind,
            hint,
        }
    }

    /// Create an expected identifier error.
    pub fn expected_identifier(token: Token) -> Self {
        let hint = match token.kind {
            TokenKind::Integer(_) => Some("identifiers cannot start with numbers".to_string()),
            TokenKind::String(_) => Some("string literals cannot be used as identifiers".to_string()),
            _ => Some(format!("expected a variable or function name, found {:?}", token.kind)),
        };
        Self::ExpectedIdentifier { span: token.span, hint }
    }

    /// Create a custom error.
    pub fn custom(span: Span, message: impl Into<String>) -> Self {
        Self::Custom {
            span,
            message: message.into(),
            hint: None,
        }
    }

    /// Create a custom error with a hint.
    pub fn custom_with_hint(span: Span, message: impl Into<String>, hint: impl Into<String>) -> Self {
        Self::Custom {
            span,
            message: message.into(),
            hint: Some(hint.into()),
        }
    }

    /// Get the span of this error.
    pub fn span(&self) -> Span {
        match self {
            Self::UnexpectedToken { span, .. } => *span,
            Self::ExpectedToken { span, .. } => *span,
            Self::ExpectedIdentifier { span, .. } => *span,
            Self::UnexpectedEof { span, .. } => *span,
            Self::InvalidResourceLiteral { span, .. } => *span,
            Self::Custom { span, .. } => *span,
        }
    }

    /// Get the hint for this error, if any.
    pub fn hint(&self) -> Option<&str> {
        match self {
            Self::UnexpectedToken { hint, .. } => hint.as_deref(),
            Self::ExpectedToken { hint, .. } => hint.as_deref(),
            Self::ExpectedIdentifier { hint, .. } => hint.as_deref(),
            Self::UnexpectedEof { hint, .. } => hint.as_deref(),
            Self::InvalidResourceLiteral { hint, .. } => hint.as_deref(),
            Self::Custom { hint, .. } => hint.as_deref(),
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

/// Generate helpful hint for unexpected token errors.
fn generate_unexpected_token_hint(_found: &TokenKind, expected: &str) -> Option<String> {
    if expected.contains("expression") {
        Some("check the syntax of your expression".to_string())
    } else {
        None
    }
}

/// Generate helpful hint for expected token errors.
fn generate_expected_token_hint(_expected: &TokenKind, found: &TokenKind) -> Option<String> {
    match found {
        TokenKind::Eof => {
            Some("unexpected end of file - check for unclosed expressions".to_string())
        }
        _ => None,
    }
}
