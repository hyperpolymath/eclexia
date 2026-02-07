// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Unbounded resource detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::{ConstraintKind, Item};

pub struct UnboundedResourceRule;

impl LintRule for UnboundedResourceRule {
    fn name(&self) -> &str {
        "unbounded_resource"
    }

    fn severity(&self) -> Severity {
        Severity::Warning
    }

    fn description(&self) -> &str {
        "Function has no resource budget constraints"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for item in &ctx.file.items {
            match item {
                Item::Function(func) => {
                    // Check if function has any resource constraints
                    let has_resource_constraints = func.constraints.iter().any(|constraint| {
                        matches!(&constraint.kind, ConstraintKind::Resource { .. })
                    });

                    if !has_resource_constraints && !func.name.starts_with("_") {
                        diagnostics.push(
                            Diagnostic::new(
                                self.severity(),
                                func.span,
                                self.name().to_string(),
                                format!(
                                    "Function '{}' has no resource budget constraints",
                                    func.name
                                ),
                            )
                            .with_suggestion(
                                "Add @requires annotation with resource constraints (e.g., @requires: energy < 1J)"
                                    .to_string(),
                            ),
                        );
                    }
                }
                Item::AdaptiveFunction(func) => {
                    // Check if adaptive function has any resource constraints
                    let has_resource_constraints = func.constraints.iter().any(|constraint| {
                        matches!(&constraint.kind, ConstraintKind::Resource { .. })
                    });

                    if !has_resource_constraints {
                        diagnostics.push(
                            Diagnostic::new(
                                self.severity(),
                                func.span,
                                self.name().to_string(),
                                format!(
                                    "Adaptive function '{}' has no resource budget constraints",
                                    func.name
                                ),
                            )
                            .with_suggestion(
                                "Add @requires annotation with resource constraints"
                                    .to_string(),
                            ),
                        );
                    }
                }
                _ => {}
            }
        }

        diagnostics
    }
}
