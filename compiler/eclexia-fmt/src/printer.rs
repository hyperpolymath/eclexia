// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! AST pretty printer for Eclexia code.

use crate::FormatConfig;
use eclexia_ast::*;

/// Pretty printer for Eclexia AST.
pub struct Printer<'a> {
    config: &'a FormatConfig,
    #[allow(dead_code)]
    source: &'a str,
    output: String,
    indent_level: usize,
    needs_indent: bool,
}

impl<'a> Printer<'a> {
    pub fn new(config: &'a FormatConfig, source: &'a str) -> Self {
        Self {
            config,
            source,
            output: String::new(),
            indent_level: 0,
            needs_indent: true,
        }
    }

    pub fn finish(self) -> String {
        self.output
    }

    /// Write a string to output.
    fn write(&mut self, s: &str) {
        if self.needs_indent && !s.is_empty() {
            self.write_indent();
            self.needs_indent = false;
        }
        self.output.push_str(s);
    }

    /// Write indentation.
    fn write_indent(&mut self) {
        let indent = if self.config.use_spaces {
            " ".repeat(self.indent_level * self.config.indent_width)
        } else {
            "\t".repeat(self.indent_level)
        };
        self.output.push_str(&indent);
    }

    /// Write a newline.
    pub fn newline(&mut self) {
        self.output.push('\n');
        self.needs_indent = true;
    }

    /// Increase indentation level.
    fn indent(&mut self) {
        self.indent_level += 1;
    }

    /// Decrease indentation level.
    fn dedent(&mut self) {
        if self.indent_level > 0 {
            self.indent_level -= 1;
        }
    }

    /// Format a top-level item.
    pub fn format_item(&mut self, item: &Item, file: &SourceFile) {
        match item {
            Item::Function(func) => self.format_function(func, file),
            Item::AdaptiveFunction(func) => self.format_adaptive_function(func, file),
            Item::TypeDef(typedef) => self.format_typedef(typedef, file),
            Item::Const(const_def) => self.format_const(const_def, file),
            Item::Import(import) => self.format_import(import),
            Item::TraitDecl(decl) => self.format_trait_decl(decl, file),
            Item::ImplBlock(block) => self.format_impl_block(block, file),
            Item::ModuleDecl(decl) => self.format_module_decl(decl, file),
            Item::EffectDecl(decl) => self.format_effect_decl(decl, file),
            Item::StaticDecl(decl) => self.format_static_decl(decl, file),
            Item::ExternBlock(block) => self.format_extern_block(block, file),
            Item::Error(_) => {} // Skip error items silently
            Item::MacroDef(_) => {} // Skip macro definitions (not yet formatted)
        }
    }

    fn format_function(&mut self, func: &Function, file: &SourceFile) {
        // Function signature
        self.write("fn ");
        self.write(func.name.as_str());
        self.write("(");

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(param.name.as_str());
            if let Some(ty) = param.ty {
                self.write(": ");
                self.format_type(ty, file);
            }
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = func.return_type {
            self.write(" -> ");
            self.format_type(ret_ty, file);
        }

        self.write(" ");
        self.format_block(&func.body, file);
    }

    fn format_adaptive_function(&mut self, func: &AdaptiveFunction, file: &SourceFile) {
        // Adaptive signature
        self.write("adaptive fn ");
        self.write(func.name.as_str());
        self.write("(");

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(param.name.as_str());
            if let Some(ty) = param.ty {
                self.write(": ");
                self.format_type(ty, file);
            }
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = func.return_type {
            self.write(" -> ");
            self.format_type(ret_ty, file);
        }

        self.write(" {");
        self.newline();
        self.indent();

        // Solutions
        for solution in &func.solutions {
            self.write(&solution.name);
            self.write(": ");
            self.format_block(&solution.body, file);
            self.newline();
        }

        self.dedent();
        self.write("}");
    }

    fn format_typedef(&mut self, typedef: &TypeDef, file: &SourceFile) {
        self.write("type ");
        self.write(typedef.name.as_str());

        match &typedef.kind {
            TypeDefKind::Alias(ty_id) => {
                self.write(" = ");
                self.format_type(*ty_id, file);
                self.write(";");
            }
            TypeDefKind::Struct(fields) => {
                self.write(" {");
                self.newline();
                self.indent();
                for field in fields {
                    self.write(field.name.as_str());
                    self.write(": ");
                    self.format_type(field.ty, file);
                    self.write(",");
                    self.newline();
                }
                self.dedent();
                self.write("}");
            }
            TypeDefKind::Enum(variants) => {
                self.write(" {");
                self.newline();
                self.indent();
                for variant in variants {
                    self.write(variant.name.as_str());
                    if let Some(fields) = &variant.fields {
                        self.write("(");
                        for (i, &field) in fields.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.format_type(field, file);
                        }
                        self.write(")");
                    }
                    self.write(",");
                    self.newline();
                }
                self.dedent();
                self.write("}");
            }
        }
    }

    fn format_const(&mut self, const_def: &ConstDef, file: &SourceFile) {
        self.write("const ");
        self.write(const_def.name.as_str());
        if let Some(ty) = const_def.ty {
            self.write(": ");
            self.format_type(ty, file);
        }
        self.write(" = ");
        self.format_expr(const_def.value, file);
        self.write(";");
    }

    fn format_import(&mut self, import: &Import) {
        self.write("import ");
        for (i, segment) in import.path.iter().enumerate() {
            if i > 0 {
                self.write("::");
            }
            self.write(segment.as_str());
        }
        if let Some(alias) = &import.alias {
            self.write(" as ");
            self.write(alias.as_str());
        }
        self.write(";");
    }

    fn format_trait_decl(&mut self, decl: &TraitDecl, file: &SourceFile) {
        self.format_visibility(&decl.visibility);
        self.write("trait ");
        self.write(decl.name.as_str());
        self.format_type_params(&decl.type_params);
        if !decl.super_traits.is_empty() {
            self.write(": ");
            for (i, bound) in decl.super_traits.iter().enumerate() {
                if i > 0 {
                    self.write(" + ");
                }
                self.format_trait_bound(bound, file);
            }
        }
        self.format_where_clause(&decl.where_clause, file);
        self.write(" {");
        self.newline();
        self.indent();

        for item in &decl.items {
            match item {
                TraitItem::Method { sig, body, .. } => {
                    self.write("fn ");
                    self.format_fn_sig(sig, file);
                    if let Some(block) = body {
                        self.write(" ");
                        self.format_block(block, file);
                    } else {
                        self.write(";");
                    }
                    self.newline();
                }
                TraitItem::AssocType { name, bounds, default, .. } => {
                    self.write("type ");
                    self.write(name.as_str());
                    if !bounds.is_empty() {
                        self.write(": ");
                        for (i, bound) in bounds.iter().enumerate() {
                            if i > 0 {
                                self.write(" + ");
                            }
                            self.format_trait_bound(bound, file);
                        }
                    }
                    if let Some(ty) = default {
                        self.write(" = ");
                        self.format_type(*ty, file);
                    }
                    self.write(";");
                    self.newline();
                }
                TraitItem::AssocConst { name, ty, default, .. } => {
                    self.write("const ");
                    self.write(name.as_str());
                    self.write(": ");
                    self.format_type(*ty, file);
                    if let Some(val) = default {
                        self.write(" = ");
                        self.format_expr(*val, file);
                    }
                    self.write(";");
                    self.newline();
                }
            }
        }

        self.dedent();
        self.write("}");
    }

    fn format_impl_block(&mut self, block: &ImplBlock, file: &SourceFile) {
        self.write("impl");
        self.format_type_params(&block.type_params);
        if let Some(trait_path) = &block.trait_path {
            self.write(" ");
            for (i, segment) in trait_path.iter().enumerate() {
                if i > 0 {
                    self.write("::");
                }
                self.write(segment.as_str());
            }
            self.write(" for ");
        } else {
            self.write(" ");
        }
        self.format_type(block.self_ty, file);
        self.format_where_clause(&block.where_clause, file);
        self.write(" {");
        self.newline();
        self.indent();

        for item in &block.items {
            match item {
                ImplItem::Method { visibility, sig, body, .. } => {
                    self.format_visibility(visibility);
                    self.write("fn ");
                    self.format_fn_sig(sig, file);
                    self.write(" ");
                    self.format_block(body, file);
                    self.newline();
                }
                ImplItem::AssocType { name, ty, .. } => {
                    self.write("type ");
                    self.write(name.as_str());
                    self.write(" = ");
                    self.format_type(*ty, file);
                    self.write(";");
                    self.newline();
                }
                ImplItem::AssocConst { name, ty, value, .. } => {
                    self.write("const ");
                    self.write(name.as_str());
                    self.write(": ");
                    self.format_type(*ty, file);
                    self.write(" = ");
                    self.format_expr(*value, file);
                    self.write(";");
                    self.newline();
                }
            }
        }

        self.dedent();
        self.write("}");
    }

    fn format_module_decl(&mut self, decl: &ModuleDecl, file: &SourceFile) {
        self.format_visibility(&decl.visibility);
        self.write("mod ");
        self.write(decl.name.as_str());
        if let Some(items) = &decl.items {
            self.write(" {");
            self.newline();
            self.indent();
            for item in items {
                self.format_item(item, file);
                self.newline();
            }
            self.dedent();
            self.write("}");
        } else {
            self.write(";");
        }
    }

    fn format_effect_decl(&mut self, decl: &EffectDecl, file: &SourceFile) {
        self.format_visibility(&decl.visibility);
        self.write("effect ");
        self.write(decl.name.as_str());
        self.format_type_params(&decl.type_params);
        self.write(" {");
        self.newline();
        self.indent();

        for op in &decl.operations {
            self.write("fn ");
            self.write(op.name.as_str());
            self.write("(");
            for (i, param) in op.params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param.name.as_str());
                if let Some(ty) = param.ty {
                    self.write(": ");
                    self.format_type(ty, file);
                }
            }
            self.write(")");
            if let Some(ret_ty) = op.return_type {
                self.write(" -> ");
                self.format_type(ret_ty, file);
            }
            self.write(";");
            self.newline();
        }

        self.dedent();
        self.write("}");
    }

    fn format_static_decl(&mut self, decl: &StaticDecl, file: &SourceFile) {
        self.format_visibility(&decl.visibility);
        if decl.mutable {
            self.write("static mut ");
        } else {
            self.write("static ");
        }
        self.write(decl.name.as_str());
        self.write(": ");
        self.format_type(decl.ty, file);
        self.write(" = ");
        self.format_expr(decl.value, file);
        self.write(";");
    }

    fn format_extern_block(&mut self, block: &ExternBlock, file: &SourceFile) {
        self.write("extern");
        if let Some(abi) = &block.abi {
            self.write(" \"");
            self.write(abi.as_str());
            self.write("\"");
        }
        self.write(" {");
        self.newline();
        self.indent();

        for item in &block.items {
            match item {
                ExternItem::Fn(sig) => {
                    self.write("fn ");
                    self.format_fn_sig(sig, file);
                    self.write(";");
                    self.newline();
                }
                ExternItem::Static { mutable, name, ty, .. } => {
                    if *mutable {
                        self.write("static mut ");
                    } else {
                        self.write("static ");
                    }
                    self.write(name.as_str());
                    self.write(": ");
                    self.format_type(*ty, file);
                    self.write(";");
                    self.newline();
                }
            }
        }

        self.dedent();
        self.write("}");
    }

    /// Format a function signature (shared helper for traits, impls, extern)
    fn format_fn_sig(&mut self, sig: &FunctionSig, file: &SourceFile) {
        self.write(sig.name.as_str());
        self.format_type_params(&sig.type_params);
        self.write("(");
        for (i, param) in sig.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(param.name.as_str());
            if let Some(ty) = param.ty {
                self.write(": ");
                self.format_type(ty, file);
            }
        }
        self.write(")");
        if let Some(ret_ty) = sig.return_type {
            self.write(" -> ");
            self.format_type(ret_ty, file);
        }
        self.format_where_clause(&sig.where_clause, file);
    }

    /// Format type parameters: `<T, U: Trait>`
    fn format_type_params(&mut self, params: &[TypeParam]) {
        if params.is_empty() {
            return;
        }
        self.write("<");
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(param.name.as_str());
            if !param.bounds.is_empty() {
                self.write(": ");
                for (j, bound) in param.bounds.iter().enumerate() {
                    if j > 0 {
                        self.write(" + ");
                    }
                    // Inline path formatting to avoid needing file
                    for (k, segment) in bound.path.iter().enumerate() {
                        if k > 0 {
                            self.write("::");
                        }
                        self.write(segment.as_str());
                    }
                }
            }
        }
        self.write(">");
    }

    /// Format a trait bound
    fn format_trait_bound(&mut self, bound: &TraitBound, file: &SourceFile) {
        for (i, segment) in bound.path.iter().enumerate() {
            if i > 0 {
                self.write("::");
            }
            self.write(segment.as_str());
        }
        if !bound.type_args.is_empty() {
            self.write("<");
            for (i, &arg) in bound.type_args.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.format_type(arg, file);
            }
            self.write(">");
        }
    }

    /// Format a where clause
    fn format_where_clause(&mut self, preds: &[WherePredicate], file: &SourceFile) {
        if preds.is_empty() {
            return;
        }
        self.newline();
        self.indent();
        self.write("where");
        self.newline();
        self.indent();
        for (i, pred) in preds.iter().enumerate() {
            self.format_type(pred.ty, file);
            self.write(": ");
            for (j, bound) in pred.bounds.iter().enumerate() {
                if j > 0 {
                    self.write(" + ");
                }
                self.format_trait_bound(bound, file);
            }
            if i < preds.len() - 1 {
                self.write(",");
            }
            self.newline();
        }
        self.dedent();
        self.dedent();
    }

    /// Format visibility modifier
    fn format_visibility(&mut self, vis: &Visibility) {
        match vis {
            Visibility::Public => self.write("pub "),
            Visibility::PubCrate => self.write("pub(crate) "),
            Visibility::Private => {}
        }
    }

    fn format_block(&mut self, block: &Block, file: &SourceFile) {
        self.write("{");
        self.newline();
        self.indent();

        // Statements
        for &stmt_id in &block.stmts {
            self.format_stmt(stmt_id, file);
            self.newline();
        }

        // Expression
        if let Some(expr_id) = block.expr {
            self.format_expr(expr_id, file);
            self.newline();
        }

        self.dedent();
        self.write("}");
    }

    fn format_stmt(&mut self, stmt_id: StmtId, file: &SourceFile) {
        let stmt = &file.stmts[stmt_id];

        match &stmt.kind {
            StmtKind::Let { pattern, mutable, ty, value } => {
                self.write("let ");
                if *mutable {
                    self.write("mut ");
                }
                self.format_pattern(pattern);
                if let Some(ty_id) = ty {
                    self.write(": ");
                    self.format_type(*ty_id, file);
                }
                self.write(" = ");
                self.format_expr(*value, file);
                self.write(";");
            }
            StmtKind::Expr(expr_id) => {
                self.format_expr(*expr_id, file);
                self.write(";");
            }
            StmtKind::Return(Some(expr_id)) => {
                self.write("return ");
                self.format_expr(*expr_id, file);
                self.write(";");
            }
            StmtKind::Return(None) => {
                self.write("return;");
            }
            StmtKind::Assign { target, value } => {
                self.format_expr(*target, file);
                self.write(" = ");
                self.format_expr(*value, file);
                self.write(";");
            }
            StmtKind::While { condition, body } => {
                self.write("while ");
                self.format_expr(*condition, file);
                self.write(" ");
                self.format_block(body, file);
            }
            StmtKind::For { pattern, iter, body } => {
                self.write("for ");
                self.format_pattern(pattern);
                self.write(" in ");
                self.format_expr(*iter, file);
                self.write(" ");
                self.format_block(body, file);
            }
            StmtKind::Loop { label, body } => {
                if let Some(lbl) = label {
                    self.write("'");
                    self.write(lbl.as_str());
                    self.write(": ");
                }
                self.write("loop ");
                self.format_block(body, file);
            }
            StmtKind::Break { label, value } => {
                self.write("break");
                if let Some(lbl) = label {
                    self.write(" '");
                    self.write(lbl.as_str());
                }
                if let Some(val) = value {
                    self.write(" ");
                    self.format_expr(*val, file);
                }
                self.write(";");
            }
            StmtKind::Continue { label } => {
                self.write("continue");
                if let Some(lbl) = label {
                    self.write(" '");
                    self.write(lbl.as_str());
                }
                self.write(";");
            }
            StmtKind::Error => {} // Skip error statements silently
        }
    }

    fn format_expr(&mut self, expr_id: ExprId, file: &SourceFile) {
        let expr = &file.exprs[expr_id];

        match &expr.kind {
            ExprKind::Literal(lit) => self.format_literal(lit),
            ExprKind::Var(name) => self.write(name.as_str()),
            ExprKind::Binary { op, lhs, rhs } => {
                self.format_expr(*lhs, file);
                self.write(" ");
                self.write(self.format_binop(*op));
                self.write(" ");
                self.format_expr(*rhs, file);
            }
            ExprKind::Unary { op, operand } => {
                self.write(self.format_unop(*op));
                self.format_expr(*operand, file);
            }
            ExprKind::Call { func, args } => {
                self.format_expr(*func, file);
                self.write("(");
                for (i, &arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_expr(arg, file);
                }
                self.write(")");
            }
            ExprKind::MethodCall { receiver, method, args } => {
                self.format_expr(*receiver, file);
                self.write(".");
                self.write(method.as_str());
                self.write("(");
                for (i, &arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_expr(arg, file);
                }
                self.write(")");
            }
            ExprKind::If { condition, then_branch, else_branch } => {
                self.write("if ");
                self.format_expr(*condition, file);
                self.write(" ");
                self.format_block(then_branch, file);
                if let Some(else_block) = else_branch {
                    self.write(" else ");
                    self.format_block(else_block, file);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.write("match ");
                self.format_expr(*scrutinee, file);
                self.write(" {");
                self.newline();
                self.indent();

                for arm in arms {
                    self.format_pattern(&arm.pattern);
                    self.write(" => ");
                    self.format_expr(arm.body, file);
                    self.write(",");
                    self.newline();
                }

                self.dedent();
                self.write("}");
            }
            ExprKind::Block(block) => self.format_block(block, file),
            ExprKind::Lambda { params, body } => {
                self.write("|");
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(param.name.as_str());
                }
                self.write("| ");
                self.format_expr(*body, file);
            }
            ExprKind::Tuple(elements) => {
                self.write("(");
                for (i, &elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_expr(elem, file);
                }
                self.write(")");
            }
            ExprKind::Array(elements) => {
                self.write("[");
                for (i, &elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_expr(elem, file);
                }
                self.write("]");
            }
            ExprKind::Struct { name, fields } => {
                self.write(name.as_str());
                self.write(" {");
                for (i, (field_name, field_expr)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(field_name.as_str());
                    self.write(": ");
                    self.format_expr(*field_expr, file);
                }
                self.write("}");
            }
            ExprKind::Index { expr, index } => {
                self.format_expr(*expr, file);
                self.write("[");
                self.format_expr(*index, file);
                self.write("]");
            }
            ExprKind::Field { expr, field } => {
                self.format_expr(*expr, file);
                self.write(".");
                self.write(field.as_str());
            }
            ExprKind::Resource(amount) => {
                // Format resource literals with no space between value and unit
                self.write(&amount.value.to_string());
                if let Some(unit) = &amount.unit {
                    self.write(unit.as_str());
                }
            }
            ExprKind::Cast { expr, target_ty } => {
                self.format_expr(*expr, file);
                self.write(" as ");
                self.format_type(*target_ty, file);
            }
            ExprKind::ArrayRepeat { value, count } => {
                self.write("[");
                self.format_expr(*value, file);
                self.write("; ");
                self.format_expr(*count, file);
                self.write("]");
            }
            ExprKind::Try(expr) => {
                self.format_expr(*expr, file);
                self.write("?");
            }
            ExprKind::Borrow { expr, mutable } => {
                if *mutable {
                    self.write("&mut ");
                } else {
                    self.write("&");
                }
                self.format_expr(*expr, file);
            }
            ExprKind::Deref(expr) => {
                self.write("*");
                self.format_expr(*expr, file);
            }
            ExprKind::AsyncBlock(block) => {
                self.write("async ");
                self.format_block(block, file);
            }
            ExprKind::Await(expr) => {
                self.format_expr(*expr, file);
                self.write(".await");
            }
            ExprKind::Handle { expr, handlers } => {
                self.write("handle ");
                self.format_expr(*expr, file);
                self.write(" {");
                self.newline();
                self.indent();
                for handler in handlers {
                    self.write(handler.effect_name.as_str());
                    self.write(".");
                    self.write(handler.op_name.as_str());
                    self.write("(");
                    for (i, param) in handler.params.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(param.name.as_str());
                        if let Some(ty) = param.ty {
                            self.write(": ");
                            self.format_type(ty, file);
                        }
                    }
                    if let Some(resume) = &handler.resume_param {
                        if !handler.params.is_empty() {
                            self.write(", ");
                        }
                        self.write("resume ");
                        self.write(resume.as_str());
                    }
                    self.write(") ");
                    self.format_block(&handler.body, file);
                    self.newline();
                }
                self.dedent();
                self.write("}");
            }
            ExprKind::ReturnExpr(Some(expr)) => {
                self.write("return ");
                self.format_expr(*expr, file);
            }
            ExprKind::ReturnExpr(None) => {
                self.write("return");
            }
            ExprKind::BreakExpr { label, value } => {
                self.write("break");
                if let Some(lbl) = label {
                    self.write(" '");
                    self.write(lbl.as_str());
                }
                if let Some(val) = value {
                    self.write(" ");
                    self.format_expr(*val, file);
                }
            }
            ExprKind::ContinueExpr { label } => {
                self.write("continue");
                if let Some(lbl) = label {
                    self.write(" '");
                    self.write(lbl.as_str());
                }
            }
            ExprKind::PathExpr(segments) => {
                for (i, segment) in segments.iter().enumerate() {
                    if i > 0 {
                        self.write("::");
                    }
                    self.write(segment.as_str());
                }
            }
            ExprKind::Error => self.write("/* error */"),
            // Concurrency primitives (not yet fully formatted)
            ExprKind::Spawn(_) => self.write("/* spawn */"),
            ExprKind::Channel { .. } => self.write("/* channel */"),
            ExprKind::Send { .. } => self.write("/* send */"),
            ExprKind::Recv(_) => self.write("/* recv */"),
            ExprKind::Select { .. } => self.write("/* select */"),
            ExprKind::YieldExpr(_) => self.write("yield"),
            ExprKind::MacroCall { name, args } => {
                self.write(name.as_str());
                self.write("!(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_expr(*arg, file);
                }
                self.write(")");
            }
        }
    }

    fn format_literal(&mut self, lit: &Literal) {
        match lit {
            Literal::Int(n) => self.write(&n.to_string()),
            Literal::Float(f) => self.write(&f.to_string()),
            Literal::String(s) => {
                self.write("\"");
                self.write(s.as_str());
                self.write("\"");
            }
            Literal::Char(c) => {
                self.write("'");
                self.write(&c.to_string());
                self.write("'");
            }
            Literal::Bool(b) => self.write(if *b { "true" } else { "false" }),
            Literal::Unit => self.write("()"),
        }
    }

    fn format_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Wildcard => self.write("_"),
            Pattern::Var(name) => self.write(name.as_str()),
            Pattern::Literal(lit) => self.format_literal(lit),
            Pattern::Tuple(patterns) => {
                self.write("(");
                for (i, pat) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_pattern(pat);
                }
                self.write(")");
            }
            Pattern::Constructor { name, fields } => {
                self.write(name.as_str());
                if !fields.is_empty() {
                    self.write("(");
                    for (i, field) in fields.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.format_pattern(field);
                    }
                    self.write(")");
                }
            }
            Pattern::Struct { name, fields, rest } => {
                self.write(name.as_str());
                self.write(" { ");
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(field.name.as_str());
                    if let Some(pat) = &field.pattern {
                        self.write(": ");
                        self.format_pattern(pat);
                    }
                }
                if *rest {
                    if !fields.is_empty() {
                        self.write(", ");
                    }
                    self.write("..");
                }
                self.write(" }");
            }
            Pattern::Slice(patterns) => {
                self.write("[");
                for (i, pat) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_pattern(pat);
                }
                self.write("]");
            }
            Pattern::Or(patterns) => {
                for (i, pat) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" | ");
                    }
                    self.format_pattern(pat);
                }
            }
            Pattern::Range { start, end, inclusive } => {
                if let Some(s) = start {
                    self.format_pattern(s);
                }
                if *inclusive {
                    self.write("..=");
                } else {
                    self.write("..");
                }
                if let Some(e) = end {
                    self.format_pattern(e);
                }
            }
            Pattern::Rest => {
                self.write("..");
            }
            Pattern::Binding { name, pattern } => {
                self.write(name.as_str());
                self.write(" @ ");
                self.format_pattern(pattern);
            }
            Pattern::Reference { pattern, mutable } => {
                if *mutable {
                    self.write("&mut ");
                } else {
                    self.write("&");
                }
                self.format_pattern(pattern);
            }
        }
    }

    fn format_type(&mut self, type_id: TypeId, file: &SourceFile) {
        let ty = &file.types[type_id];

        match &ty.kind {
            TypeKind::Named { name, args } => {
                self.write(name.as_str());
                if !args.is_empty() {
                    self.write("<");
                    for (i, &arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.format_type(arg, file);
                    }
                    self.write(">");
                }
            }
            TypeKind::Function { params, ret } => {
                self.write("fn(");
                for (i, &param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_type(param, file);
                }
                self.write(") -> ");
                self.format_type(*ret, file);
            }
            TypeKind::Tuple(types) => {
                self.write("(");
                for (i, &ty) in types.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.format_type(ty, file);
                }
                self.write(")");
            }
            TypeKind::Array { elem, size } => {
                self.write("[");
                self.format_type(*elem, file);
                if let Some(n) = size {
                    self.write("; ");
                    self.write(&n.to_string());
                }
                self.write("]");
            }
            TypeKind::Resource { base, dimension } => {
                self.write("resource<");
                self.write(base.as_str());
                self.write(", ");
                self.write(&format!("{:?}", dimension));
                self.write(">");
            }
            TypeKind::Reference { ty, mutable } => {
                if *mutable {
                    self.write("&mut ");
                } else {
                    self.write("&");
                }
                self.format_type(*ty, file);
            }
            TypeKind::Optional(ty) => {
                self.format_type(*ty, file);
                self.write("?");
            }
            TypeKind::Infer => self.write("_"),
            TypeKind::Error => self.write("/* error */"),
        }
    }

    fn format_binop(&self, op: BinaryOp) -> &'static str {
        match op {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Rem => "%",
            BinaryOp::Pow => "**",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::And => "&&",
            BinaryOp::Or => "||",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::Shl => "<<",
            BinaryOp::Shr => ">>",
            BinaryOp::Range => "..",
            BinaryOp::RangeInclusive => "..=",
        }
    }

    fn format_unop(&self, op: UnaryOp) -> &'static str {
        match op {
            UnaryOp::Neg => "-",
            UnaryOp::Not => "!",
            UnaryOp::BitNot => "~",
        }
    }
}
