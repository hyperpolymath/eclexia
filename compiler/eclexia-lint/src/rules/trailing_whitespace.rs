// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Trailing whitespace detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::span::Span;

pub struct TrailingWhitespaceRule;

impl LintRule for TrailingWhitespaceRule {
    fn name(&self) -> &str {
        "trailing_whitespace"
    }

    fn severity(&self) -> Severity {
        Severity::Info
    }

    fn description(&self) -> &str {
        "Line has trailing whitespace"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let mut offset = 0usize;
        for line in ctx.source.lines() {
            let trimmed = line.trim_end();

            if trimmed.len() < line.len() {
                // Found trailing whitespace
                let start = offset + trimmed.len();
                let end = offset + line.len();
                let span = Span::new(start as u32, end as u32);

                diagnostics.push(
                    Diagnostic::new(
                        self.severity(),
                        span,
                        self.name().to_string(),
                        "Line has trailing whitespace".to_string(),
                    )
                    .with_suggestion("Remove trailing whitespace".to_string()),
                );
            }

            offset += line.len() + 1; // +1 for newline
        }

        diagnostics
    }
}
