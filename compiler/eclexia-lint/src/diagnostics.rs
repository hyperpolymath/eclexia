// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Diagnostic reporting for lint violations.

use eclexia_ast::span::Span;

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Information/suggestion.
    Info,
    /// Warning that doesn't prevent compilation.
    Warning,
    /// Error that should prevent compilation.
    Error,
}

impl Severity {
    pub fn as_str(&self) -> &'static str {
        match self {
            Severity::Info => "info",
            Severity::Warning => "warning",
            Severity::Error => "error",
        }
    }
}

/// A diagnostic message for a lint violation.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Severity of the issue.
    pub severity: Severity,
    /// Source location span.
    pub span: Span,
    /// Name of the rule that triggered this diagnostic.
    pub rule: String,
    /// Human-readable message.
    pub message: String,
    /// Optional suggestion for fixing the issue.
    pub suggestion: Option<String>,
}

impl Diagnostic {
    /// Create a new diagnostic.
    pub fn new(severity: Severity, span: Span, rule: String, message: String) -> Self {
        Self {
            severity,
            span,
            rule,
            message,
            suggestion: None,
        }
    }

    /// Add a suggestion for fixing this issue.
    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    /// Format the diagnostic with source context.
    pub fn format_with_source(&self, source: &str) -> String {
        let (line, col) = offset_to_line_col(source, self.span.start as usize);
        let line_text = source.lines().nth(line).unwrap_or("");

        let mut output = String::new();

        // Main message
        output.push_str(&format!(
            "{}:{}:{}: {}: {} [{}]\n",
            "file",
            line + 1,
            col + 1,
            self.severity.as_str(),
            self.message,
            self.rule
        ));

        // Source line
        output.push_str(&format!("  {} | {}\n", line + 1, line_text));

        // Caret indicator
        let indent = format!("  {} | ", line + 1).len() + col;
        output.push_str(&format!("{}{}\n", " ".repeat(indent), "^"));

        // Suggestion
        if let Some(suggestion) = &self.suggestion {
            output.push_str(&format!("  = help: {}\n", suggestion));
        }

        output
    }
}

/// Convert byte offset to (line, column).
fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 0;
    let mut col = 0;
    let mut current_offset = 0;

    for ch in source.chars() {
        if current_offset >= offset {
            break;
        }

        if ch == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }

        current_offset += ch.len_utf8();
    }

    (line, col)
}
