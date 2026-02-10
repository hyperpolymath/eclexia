// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Negative resource detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::{ExprId, ExprKind, Item};

pub struct NegativeResourceRule;

impl LintRule for NegativeResourceRule {
    fn name(&self) -> &str {
        "negative_resource"
    }

    fn severity(&self) -> Severity {
        Severity::Error
    }

    fn description(&self) -> &str {
        "Resource amount cannot be negative"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for item in &ctx.file.items {
            match item {
                Item::Function(func) => {
                    check_block_for_negative_resources(
                        &func.body.stmts,
                        ctx,
                        &mut diagnostics,
                        self,
                    );
                    if let Some(expr_id) = func.body.expr {
                        check_expr_for_negative_resources(expr_id, ctx, &mut diagnostics, self);
                    }
                }
                Item::AdaptiveFunction(func) => {
                    for solution in &func.solutions {
                        check_block_for_negative_resources(
                            &solution.body.stmts,
                            ctx,
                            &mut diagnostics,
                            self,
                        );
                        if let Some(expr_id) = solution.body.expr {
                            check_expr_for_negative_resources(expr_id, ctx, &mut diagnostics, self);
                        }
                    }
                }
                _ => {}
            }
        }

        diagnostics
    }
}

fn check_block_for_negative_resources(
    stmts: &[eclexia_ast::StmtId],
    ctx: &LintContext,
    diagnostics: &mut Vec<Diagnostic>,
    rule: &NegativeResourceRule,
) {
    for &stmt_id in stmts {
        let stmt = &ctx.file.stmts[stmt_id];
        match &stmt.kind {
            eclexia_ast::StmtKind::Let { value, .. } => {
                check_expr_for_negative_resources(*value, ctx, diagnostics, rule);
            }
            eclexia_ast::StmtKind::Expr(expr_id) => {
                check_expr_for_negative_resources(*expr_id, ctx, diagnostics, rule);
            }
            eclexia_ast::StmtKind::Return(Some(expr_id)) => {
                check_expr_for_negative_resources(*expr_id, ctx, diagnostics, rule);
            }
            _ => {}
        }
    }
}

fn check_expr_for_negative_resources(
    expr_id: ExprId,
    ctx: &LintContext,
    diagnostics: &mut Vec<Diagnostic>,
    rule: &NegativeResourceRule,
) {
    let expr = &ctx.file.exprs[expr_id];

    match &expr.kind {
        ExprKind::Resource(amount) => {
            if amount.value < 0.0 {
                diagnostics.push(
                    Diagnostic::new(
                        rule.severity(),
                        expr.span,
                        rule.name().to_string(),
                        format!("Resource amount cannot be negative: {}", amount.value),
                    )
                    .with_suggestion("Resource amounts must be non-negative".to_string()),
                );
            }
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            check_expr_for_negative_resources(*lhs, ctx, diagnostics, rule);
            check_expr_for_negative_resources(*rhs, ctx, diagnostics, rule);
        }
        ExprKind::Unary { operand, .. } => {
            check_expr_for_negative_resources(*operand, ctx, diagnostics, rule);
        }
        ExprKind::Call { func, args } => {
            check_expr_for_negative_resources(*func, ctx, diagnostics, rule);
            for &arg in args {
                check_expr_for_negative_resources(arg, ctx, diagnostics, rule);
            }
        }
        _ => {}
    }
}
