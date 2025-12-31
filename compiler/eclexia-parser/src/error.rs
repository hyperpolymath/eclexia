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
    },

    #[error("expected {expected:?}, found {found:?}")]
    ExpectedToken {
        span: Span,
        expected: TokenKind,
        found: TokenKind,
    },

    #[error("expected identifier")]
    ExpectedIdentifier { span: Span },

    #[error("unexpected end of file")]
    UnexpectedEof { span: Span },

    #[error("invalid resource literal")]
    InvalidResourceLiteral { span: Span },

    #[error("{message}")]
    Custom { span: Span, message: String },
}

impl ParseError {
    /// Create an unexpected token error.
    pub fn unexpected_token(token: Token, expected: &str) -> Self {
        Self::UnexpectedToken {
            span: token.span,
            found: token.kind,
            expected: expected.to_string(),
        }
    }

    /// Create an expected token error.
    pub fn expected_token(expected: TokenKind, found: Token) -> Self {
        Self::ExpectedToken {
            span: found.span,
            expected,
            found: found.kind,
        }
    }

    /// Create an expected identifier error.
    pub fn expected_identifier(token: Token) -> Self {
        Self::ExpectedIdentifier { span: token.span }
    }

    /// Create a custom error.
    pub fn custom(span: Span, message: impl Into<String>) -> Self {
        Self::Custom {
            span,
            message: message.into(),
        }
    }

    /// Get the span of this error.
    pub fn span(&self) -> Span {
        match self {
            Self::UnexpectedToken { span, .. } => *span,
            Self::ExpectedToken { span, .. } => *span,
            Self::ExpectedIdentifier { span } => *span,
            Self::UnexpectedEof { span } => *span,
            Self::InvalidResourceLiteral { span } => *span,
            Self::Custom { span, .. } => *span,
        }
    }

    /// Format this error with line:column information from source.
    pub fn format_with_source(&self, source: &str) -> String {
        let span = self.span();
        let location = span.format_location(source);
        format!("{}: {}", location, self)
    }
}
