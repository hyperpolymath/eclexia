// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Long line detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::span::Span;

pub struct LongLineRule;

impl LintRule for LongLineRule {
    fn name(&self) -> &str {
        "long_line"
    }

    fn severity(&self) -> Severity {
        Severity::Info
    }

    fn description(&self) -> &str {
        "Line exceeds maximum length"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let max_length = ctx.config.max_line_length;

        let mut offset = 0usize;
        for line in ctx.source.lines() {
            let line_length = line.chars().count();

            if line_length > max_length {
                let span = Span::new(offset as u32, (offset + line.len()) as u32);
                diagnostics.push(
                    Diagnostic::new(
                        self.severity(),
                        span,
                        self.name().to_string(),
                        format!(
                            "Line length {} exceeds maximum of {}",
                            line_length, max_length
                        ),
                    )
                    .with_suggestion("Consider breaking this line into multiple lines".to_string()),
                );
            }

            offset += line.len() + 1; // +1 for newline
        }

        diagnostics
    }
}
