// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Unreachable code detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::{Item, StmtKind};

pub struct UnreachableCodeRule;

impl LintRule for UnreachableCodeRule {
    fn name(&self) -> &str {
        "unreachable_code"
    }

    fn severity(&self) -> Severity {
        Severity::Warning
    }

    fn description(&self) -> &str {
        "Code after return statement is unreachable"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for item in &ctx.file.items {
            if let Item::Function(func) = item {
                let mut found_return = false;

                for &stmt_id in &func.body.stmts {
                    let stmt = &ctx.file.stmts[stmt_id];

                    if found_return {
                        diagnostics.push(Diagnostic::new(
                            self.severity(),
                            stmt.span,
                            self.name().to_string(),
                            "Unreachable code after return statement".to_string(),
                        ));
                    }

                    if matches!(&stmt.kind, StmtKind::Return(_)) {
                        found_return = true;
                    }
                }
            }
        }

        diagnostics
    }
}
