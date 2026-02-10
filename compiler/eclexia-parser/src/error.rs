// SPDX-License-Identifier: PMPL-1.0-or-later
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
    /// An unexpected token was encountered while parsing.
    #[error("unexpected token {found:?}, expected {expected}")]
    UnexpectedToken {
        /// Source location of the unexpected token.
        span: Span,
        /// The token that was found.
        found: TokenKind,
        /// Description of what was expected.
        expected: String,
        /// Optional hint for fixing the error.
        hint: Option<String>,
    },

    /// A specific expected token was not found.
    #[error("expected {expected:?}, found {found:?}")]
    ExpectedToken {
        /// Source location of the error.
        span: Span,
        /// The token kind that was expected.
        expected: TokenKind,
        /// The token kind that was found instead.
        found: TokenKind,
        /// Optional hint for fixing the error.
        hint: Option<String>,
    },

    /// An identifier was expected but not found.
    #[error("expected identifier")]
    ExpectedIdentifier {
        /// Source location of the error.
        span: Span,
        /// Optional hint for fixing the error.
        hint: Option<String>,
    },

    /// Unexpected end of file while parsing.
    #[error("unexpected end of file")]
    UnexpectedEof {
        /// Source location at end of file.
        span: Span,
        /// Optional hint for fixing the error.
        hint: Option<String>,
    },

    /// An invalid resource literal was encountered.
    #[error("invalid resource literal")]
    InvalidResourceLiteral {
        /// Source location of the invalid literal.
        span: Span,
        /// Optional hint for fixing the error.
        hint: Option<String>,
    },

    /// A custom error with a freeform message.
    #[error("{message}")]
    Custom {
        /// Source location of the error.
        span: Span,
        /// The error message.
        message: String,
        /// Optional hint for fixing the error.
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
            TokenKind::String(_) => {
                Some("string literals cannot be used as identifiers".to_string())
            }
            _ => Some(format!(
                "expected a variable or function name, found {:?}",
                token.kind
            )),
        };
        Self::ExpectedIdentifier {
            span: token.span,
            hint,
        }
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
    pub fn custom_with_hint(
        span: Span,
        message: impl Into<String>,
        hint: impl Into<String>,
    ) -> Self {
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
fn generate_unexpected_token_hint(found: &TokenKind, expected: &str) -> Option<String> {
    match (found, expected) {
        (TokenKind::RBrace, "expression") => {
            Some("unexpected `}` — did you forget an expression before the block end?".to_string())
        }
        (TokenKind::Semi, "expression") => {
            Some("unexpected `;` — perhaps remove the semicolon or add an expression".to_string())
        }
        (TokenKind::Eq, "expression") => {
            Some("unexpected `=` — did you mean `==` for comparison?".to_string())
        }
        (TokenKind::Eof, _) => {
            Some("unexpected end of file — check for unclosed delimiters".to_string())
        }
        (_, "item") => {
            Some("expected a top-level item: fn, def, type, struct, trait, impl, mod, use, const, static, or extern".to_string())
        }
        (_, s) if s.contains("expression") => {
            Some("check the syntax of your expression".to_string())
        }
        _ => None,
    }
}

/// Generate helpful hint for expected token errors.
fn generate_expected_token_hint(expected: &TokenKind, found: &TokenKind) -> Option<String> {
    match (expected, found) {
        (_, TokenKind::Eof) => {
            Some("unexpected end of file — check for unclosed delimiters".to_string())
        }
        (TokenKind::RParen, _) => Some("unclosed parenthesis — add a closing `)`".to_string()),
        (TokenKind::RBracket, _) => Some("unclosed bracket — add a closing `]`".to_string()),
        (TokenKind::RBrace, _) => Some("unclosed brace — add a closing `}`".to_string()),
        (TokenKind::Semi, _) => {
            Some("consider adding a `;` at the end of this statement".to_string())
        }
        (TokenKind::Colon, TokenKind::Eq) => {
            Some("did you mean `: Type =` instead of `=`?".to_string())
        }
        (TokenKind::Arrow, _) => Some("expected `->` for return type annotation".to_string()),
        _ => None,
    }
}
