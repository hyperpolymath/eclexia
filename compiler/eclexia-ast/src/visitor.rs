// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! AST Visitor framework for Eclexia.
//!
//! Provides a trait-based visitor pattern for traversing the arena-allocated
//! AST. The visitor resolves arena indices automatically.
//!
//! # Usage
//!
//! ```ignore
//! struct MyVisitor;
//! impl Visitor for MyVisitor {
//!     fn visit_expr(&mut self, expr: &Expr, id: ExprId, file: &SourceFile) {
//!         // Custom logic here
//!         walk_expr(self, expr, file); // Continue traversal
//!     }
//! }
//! let mut v = MyVisitor;
//! visit_source_file(&mut v, &source_file);
//! ```

use crate::{
    AdaptiveFunction, Block, EffectHandler, Expr, ExprId, ExprKind, Function,
    ImplBlock, Item, MatchArm, Param, Pattern, SourceFile, Stmt,
    StmtId, StmtKind, TraitDecl,
};

/// Trait for visiting AST nodes. All methods have default implementations
/// that continue the traversal.
pub trait Visitor: Sized {
    fn visit_item(&mut self, item: &Item, file: &SourceFile) {
        walk_item(self, item, file);
    }
    fn visit_function(&mut self, func: &Function, file: &SourceFile) {
        walk_function(self, func, file);
    }
    fn visit_adaptive_function(&mut self, func: &AdaptiveFunction, file: &SourceFile) {
        walk_adaptive_function(self, func, file);
    }
    fn visit_stmt(&mut self, stmt: &Stmt, _id: StmtId, file: &SourceFile) {
        walk_stmt(self, stmt, file);
    }
    fn visit_expr(&mut self, expr: &Expr, _id: ExprId, file: &SourceFile) {
        walk_expr(self, expr, file);
    }
    fn visit_pattern(&mut self, _pattern: &Pattern, _file: &SourceFile) {}
    fn visit_block(&mut self, block: &Block, file: &SourceFile) {
        walk_block(self, block, file);
    }
    fn visit_param(&mut self, _param: &Param, _file: &SourceFile) {}
    fn visit_match_arm(&mut self, arm: &MatchArm, file: &SourceFile) {
        self.visit_pattern(&arm.pattern, file);
        if let Some(guard) = arm.guard {
            self.visit_expr_id(guard, file);
        }
        self.visit_expr_id(arm.body, file);
    }
    fn visit_effect_handler(&mut self, handler: &EffectHandler, file: &SourceFile) {
        for p in &handler.params {
            self.visit_param(p, file);
        }
        self.visit_block(&handler.body, file);
    }

    /// Resolve and visit an expression by arena index.
    fn visit_expr_id(&mut self, id: ExprId, file: &SourceFile) {
        let expr = &file.exprs[id];
        self.visit_expr(expr, id, file);
    }

    /// Resolve and visit a statement by arena index.
    fn visit_stmt_id(&mut self, id: StmtId, file: &SourceFile) {
        let stmt = &file.stmts[id];
        self.visit_stmt(stmt, id, file);
    }
}

/// Visit all items in a source file.
pub fn visit_source_file<V: Visitor>(visitor: &mut V, file: &SourceFile) {
    for item in &file.items {
        visitor.visit_item(item, file);
    }
}

/// Walk an item, visiting its children.
pub fn walk_item<V: Visitor>(visitor: &mut V, item: &Item, file: &SourceFile) {
    match item {
        Item::Function(f) => visitor.visit_function(f, file),
        Item::AdaptiveFunction(af) => visitor.visit_adaptive_function(af, file),
        Item::Const(c) => {
            visitor.visit_expr_id(c.value, file);
        }
        Item::ModuleDecl(m) => {
            if let Some(items) = &m.items {
                for sub_item in items {
                    visitor.visit_item(sub_item, file);
                }
            }
        }
        Item::TraitDecl(t) => walk_trait_decl(visitor, t, file),
        Item::ImplBlock(i) => walk_impl_block(visitor, i, file),
        Item::StaticDecl(s) => {
            visitor.visit_expr_id(s.value, file);
        }
        // Leaf items — no expression children
        Item::TypeDef(_) | Item::Import(_) | Item::EffectDecl(_)
        | Item::ExternBlock(_) | Item::MacroDef(_) | Item::Error(_) => {}
    }
}

pub fn walk_function<V: Visitor>(visitor: &mut V, func: &Function, file: &SourceFile) {
    for param in &func.params {
        visitor.visit_param(param, file);
    }
    visitor.visit_block(&func.body, file);
}

pub fn walk_adaptive_function<V: Visitor>(
    visitor: &mut V,
    func: &AdaptiveFunction,
    file: &SourceFile,
) {
    for param in &func.params {
        visitor.visit_param(param, file);
    }
    for solution in &func.solutions {
        if let Some(when) = solution.when_clause {
            visitor.visit_expr_id(when, file);
        }
        visitor.visit_block(&solution.body, file);
    }
}

pub fn walk_block<V: Visitor>(visitor: &mut V, block: &Block, file: &SourceFile) {
    for stmt_id in &block.stmts {
        visitor.visit_stmt_id(*stmt_id, file);
    }
    if let Some(tail) = block.expr {
        visitor.visit_expr_id(tail, file);
    }
}

pub fn walk_stmt<V: Visitor>(visitor: &mut V, stmt: &Stmt, file: &SourceFile) {
    match &stmt.kind {
        StmtKind::Let { value, .. } => visitor.visit_expr_id(*value, file),
        StmtKind::Assign { target, value, .. } => {
            visitor.visit_expr_id(*target, file);
            visitor.visit_expr_id(*value, file);
        }
        StmtKind::Expr(expr_id) => visitor.visit_expr_id(*expr_id, file),
        StmtKind::Return(val) => {
            if let Some(v) = val { visitor.visit_expr_id(*v, file); }
        }
        StmtKind::While { condition, body, .. } => {
            visitor.visit_expr_id(*condition, file);
            visitor.visit_block(body, file);
        }
        StmtKind::For { iter, body, pattern, .. } => {
            visitor.visit_pattern(pattern, file);
            visitor.visit_expr_id(*iter, file);
            visitor.visit_block(body, file);
        }
        StmtKind::Loop { body, .. } => visitor.visit_block(body, file),
        StmtKind::Break { value, .. } => {
            if let Some(v) = value { visitor.visit_expr_id(*v, file); }
        }
        StmtKind::Continue { .. } | StmtKind::Error => {}
    }
}

pub fn walk_expr<V: Visitor>(visitor: &mut V, expr: &Expr, file: &SourceFile) {
    match &expr.kind {
        // Leaf nodes
        ExprKind::Literal(_) | ExprKind::Var(_) | ExprKind::PathExpr(_)
        | ExprKind::ContinueExpr { .. } | ExprKind::Error => {}

        // Resource literal
        ExprKind::Resource { .. } => {}

        // Binary / Unary
        ExprKind::Binary { lhs, rhs, .. } => {
            visitor.visit_expr_id(*lhs, file);
            visitor.visit_expr_id(*rhs, file);
        }
        ExprKind::Unary { operand, .. } => {
            visitor.visit_expr_id(*operand, file);
        }

        // Calls
        ExprKind::Call { func, args, .. } => {
            visitor.visit_expr_id(*func, file);
            for arg in args { visitor.visit_expr_id(*arg, file); }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            visitor.visit_expr_id(*receiver, file);
            for arg in args { visitor.visit_expr_id(*arg, file); }
        }

        // Access
        ExprKind::Field { expr, .. } => visitor.visit_expr_id(*expr, file),
        ExprKind::Index { expr, index, .. } => {
            visitor.visit_expr_id(*expr, file);
            visitor.visit_expr_id(*index, file);
        }

        // Control flow
        ExprKind::If { condition, then_branch, else_branch, .. } => {
            visitor.visit_expr_id(*condition, file);
            visitor.visit_block(then_branch, file);
            if let Some(eb) = else_branch { visitor.visit_block(eb, file); }
        }
        ExprKind::Match { scrutinee, arms, .. } => {
            visitor.visit_expr_id(*scrutinee, file);
            for arm in arms { visitor.visit_match_arm(arm, file); }
        }

        // Block
        ExprKind::Block(block) => visitor.visit_block(block, file),

        // Return / Break
        ExprKind::ReturnExpr(val) => {
            if let Some(v) = val { visitor.visit_expr_id(*v, file); }
        }
        ExprKind::BreakExpr { value, .. } => {
            if let Some(v) = value { visitor.visit_expr_id(*v, file); }
        }

        // Collections
        ExprKind::Tuple(elems) | ExprKind::Array(elems) => {
            for e in elems { visitor.visit_expr_id(*e, file); }
        }
        ExprKind::ArrayRepeat { value, count, .. } => {
            visitor.visit_expr_id(*value, file);
            visitor.visit_expr_id(*count, file);
        }
        ExprKind::Struct { fields, .. } => {
            for (_, val) in fields { visitor.visit_expr_id(*val, file); }
        }

        // Lambda
        ExprKind::Lambda { params, body, .. } => {
            for p in params { visitor.visit_param(p, file); }
            visitor.visit_expr_id(*body, file);
        }

        // Cast / Try
        ExprKind::Cast { expr, .. } => visitor.visit_expr_id(*expr, file),
        ExprKind::Try(inner) => visitor.visit_expr_id(*inner, file),
        ExprKind::Borrow { expr: inner, .. } => visitor.visit_expr_id(*inner, file),
        ExprKind::Deref(inner) => visitor.visit_expr_id(*inner, file),

        // Async / Concurrency
        ExprKind::AsyncBlock(block) => visitor.visit_block(block, file),
        ExprKind::Await(inner) | ExprKind::Spawn(inner) => {
            visitor.visit_expr_id(*inner, file);
        }
        ExprKind::Channel { .. } => {}
        ExprKind::Send { channel, value, .. } => {
            visitor.visit_expr_id(*channel, file);
            visitor.visit_expr_id(*value, file);
        }
        ExprKind::Recv(channel) => visitor.visit_expr_id(*channel, file),
        ExprKind::YieldExpr(val) => {
            if let Some(v) = val { visitor.visit_expr_id(*v, file); }
        }

        // Select / Handle
        ExprKind::Select { arms, .. } => {
            for arm in arms {
                visitor.visit_expr_id(arm.channel, file);
                visitor.visit_expr_id(arm.body, file);
            }
        }
        ExprKind::Handle { expr, handlers, .. } => {
            visitor.visit_expr_id(*expr, file);
            for h in handlers { visitor.visit_effect_handler(h, file); }
        }

        // Macro
        ExprKind::MacroCall { args, .. } => {
            for arg in args { visitor.visit_expr_id(*arg, file); }
        }
    }
}

pub fn walk_trait_decl<V: Visitor>(visitor: &mut V, decl: &TraitDecl, file: &SourceFile) {
    for item in &decl.items {
        match item {
            crate::TraitItem::Method { sig, body: Some(body), .. } => {
                for p in &sig.params { visitor.visit_param(p, file); }
                visitor.visit_block(body, file);
            }
            crate::TraitItem::AssocConst { default: Some(val), .. } => {
                visitor.visit_expr_id(*val, file);
            }
            _ => {}
        }
    }
}

pub fn walk_impl_block<V: Visitor>(visitor: &mut V, block: &ImplBlock, file: &SourceFile) {
    for item in &block.items {
        match item {
            crate::ImplItem::Method { sig, body, .. } => {
                for p in &sig.params { visitor.visit_param(p, file); }
                visitor.visit_block(body, file);
            }
            crate::ImplItem::AssocConst { value, .. } => {
                visitor.visit_expr_id(*value, file);
            }
            _ => {}
        }
    }
}
