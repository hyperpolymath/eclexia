// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! AST pretty printer for Eclexia code.

use crate::FormatConfig;
use eclexia_ast::*;
use smol_str::SmolStr;

/// Pretty printer for Eclexia AST.
pub struct Printer<'a> {
    config: &'a FormatConfig,
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
            StmtKind::Let { name, ty, value } => {
                self.write("let ");
                self.write(name.as_str());
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
                self.write(target.as_str());
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
            StmtKind::For { name, iter, body } => {
                self.write("for ");
                self.write(name.as_str());
                self.write(" in ");
                self.format_expr(*iter, file);
                self.write(" ");
                self.format_block(body, file);
            }
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
            ExprKind::Error => self.write("/* error */"),
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
