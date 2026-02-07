// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Unused variable detection.

use crate::{Diagnostic, LintContext, LintRule, Severity};
use eclexia_ast::{ExprId, ExprKind, Item, StmtKind};
use std::collections::HashSet;

pub struct UnusedVariableRule;

impl LintRule for UnusedVariableRule {
    fn name(&self) -> &str {
        "unused_variable"
    }

    fn severity(&self) -> Severity {
        Severity::Warning
    }

    fn description(&self) -> &str {
        "Variable is defined but never used"
    }

    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for item in &ctx.file.items {
            if let Item::Function(func) = item {
                let mut defined_vars = HashSet::new();
                let mut used_vars = HashSet::new();

                // Collect defined variables from let statements
                for &stmt_id in &func.body.stmts {
                    let stmt = &ctx.file.stmts[stmt_id];
                    if let StmtKind::Let { name, .. } = &stmt.kind {
                        defined_vars.insert((name.clone(), stmt.span));
                    }
                }

                // Collect used variables
                for &stmt_id in &func.body.stmts {
                    collect_used_vars(stmt_id, ctx, &mut used_vars);
                }
                if let Some(expr_id) = func.body.expr {
                    collect_used_vars_expr(expr_id, ctx, &mut used_vars);
                }

                // Find unused variables
                for (name, span) in defined_vars {
                    if !used_vars.contains(&name) && !name.starts_with('_') {
                        diagnostics.push(
                            Diagnostic::new(
                                self.severity(),
                                span,
                                self.name().to_string(),
                                format!("Variable '{}' is defined but never used", name),
                            )
                            .with_suggestion(format!(
                                "Consider prefixing with underscore: _{} or removing it",
                                name
                            )),
                        );
                    }
                }
            }
        }

        diagnostics
    }
}

fn collect_used_vars(stmt_id: eclexia_ast::StmtId, ctx: &LintContext, used: &mut HashSet<smol_str::SmolStr>) {
    let stmt = &ctx.file.stmts[stmt_id];
    match &stmt.kind {
        StmtKind::Let { value, .. } => {
            collect_used_vars_expr(*value, ctx, used);
        }
        StmtKind::Expr(expr_id) => {
            collect_used_vars_expr(*expr_id, ctx, used);
        }
        StmtKind::Return(Some(expr_id)) => {
            collect_used_vars_expr(*expr_id, ctx, used);
        }
        StmtKind::Return(None) => {}
        StmtKind::While { condition, body } => {
            collect_used_vars_expr(*condition, ctx, used);
            for &stmt_id in &body.stmts {
                collect_used_vars(stmt_id, ctx, used);
            }
        }
        StmtKind::For { iter, body, .. } => {
            collect_used_vars_expr(*iter, ctx, used);
            for &stmt_id in &body.stmts {
                collect_used_vars(stmt_id, ctx, used);
            }
        }
        StmtKind::Assign { target, value } => {
            // Mark target as used
            used.insert(target.clone());
            collect_used_vars_expr(*value, ctx, used);
        }
    }
}

fn collect_used_vars_expr(expr_id: ExprId, ctx: &LintContext, used: &mut HashSet<smol_str::SmolStr>) {
    let expr = &ctx.file.exprs[expr_id];
    match &expr.kind {
        ExprKind::Var(name) => {
            used.insert(name.clone());
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_used_vars_expr(*lhs, ctx, used);
            collect_used_vars_expr(*rhs, ctx, used);
        }
        ExprKind::Unary { operand, .. } => {
            collect_used_vars_expr(*operand, ctx, used);
        }
        ExprKind::Call { func, args } => {
            collect_used_vars_expr(*func, ctx, used);
            for &arg in args {
                collect_used_vars_expr(arg, ctx, used);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            collect_used_vars_expr(*receiver, ctx, used);
            for &arg in args {
                collect_used_vars_expr(arg, ctx, used);
            }
        }
        ExprKind::Field { expr, .. } => {
            collect_used_vars_expr(*expr, ctx, used);
        }
        ExprKind::Index { expr, index } => {
            collect_used_vars_expr(*expr, ctx, used);
            collect_used_vars_expr(*index, ctx, used);
        }
        ExprKind::If { condition, then_branch, else_branch } => {
            collect_used_vars_expr(*condition, ctx, used);
            for &stmt_id in &then_branch.stmts {
                collect_used_vars(stmt_id, ctx, used);
            }
            if let Some(expr_id) = then_branch.expr {
                collect_used_vars_expr(expr_id, ctx, used);
            }
            if let Some(else_block) = else_branch {
                for &stmt_id in &else_block.stmts {
                    collect_used_vars(stmt_id, ctx, used);
                }
                if let Some(expr_id) = else_block.expr {
                    collect_used_vars_expr(expr_id, ctx, used);
                }
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            collect_used_vars_expr(*scrutinee, ctx, used);
            for arm in arms {
                collect_used_vars_expr(arm.body, ctx, used);
            }
        }
        ExprKind::Block(block) => {
            for &stmt_id in &block.stmts {
                collect_used_vars(stmt_id, ctx, used);
            }
            if let Some(expr_id) = block.expr {
                collect_used_vars_expr(expr_id, ctx, used);
            }
        }
        ExprKind::Lambda { body, .. } => {
            collect_used_vars_expr(*body, ctx, used);
        }
        ExprKind::Tuple(exprs) | ExprKind::Array(exprs) => {
            for &expr_id in exprs {
                collect_used_vars_expr(expr_id, ctx, used);
            }
        }
        ExprKind::Struct { fields, .. } => {
            for (_, expr_id) in fields {
                collect_used_vars_expr(*expr_id, ctx, used);
            }
        }
        _ => {}
    }
}
