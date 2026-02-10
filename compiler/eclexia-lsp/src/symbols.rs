// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Symbol resolution and scope tracking for LSP features.

use eclexia_ast::span::Span;
use eclexia_ast::{
    Block, ExprId, ExprKind, ExternItem, Ident, ImplItem, Item, Pattern, SourceFile, StmtId,
    StmtKind,
};
use std::collections::HashMap;

/// A symbol in the program (variable, function, type, etc.)
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name
    pub name: Ident,
    /// Symbol kind (function, variable, type, etc.)
    pub kind: SymbolKind,
    /// Location where the symbol is defined
    pub definition_span: Span,
    /// Documentation comment (if any)
    pub doc: Option<String>,
}

/// Kind of symbol
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Function,
    AdaptiveFunction,
    TypeDef,
    Const,
    Variable,
    Parameter,
    Method,
    Field,
    EnumVariant,
    Module,
    Static,
    Effect,
    Trait,
}

/// A scope containing symbol bindings
#[derive(Debug)]
pub struct Scope {
    /// Parent scope (None for global scope)
    parent: Option<ScopeId>,
    /// Symbols defined in this scope
    symbols: HashMap<Ident, Symbol>,
    /// Span of this scope
    #[allow(dead_code)]
    span: Span,
}

/// Scope identifier
pub type ScopeId = usize;

/// A reference to a symbol (usage site)
#[derive(Debug, Clone)]
pub struct SymbolReference {
    /// Name of the referenced symbol
    pub name: Ident,
    /// Location of the reference
    pub span: Span,
    /// Kind of reference (read, write, call, etc.)
    pub kind: ReferenceKind,
}

/// Kind of symbol reference
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReferenceKind {
    Read,
    Write,
    Call,
    TypeAnnotation,
}

/// Symbol table for a source file
#[derive(Debug)]
pub struct SymbolTable {
    /// All scopes in the file
    scopes: Vec<Scope>,
    /// Global scope ID (always 0)
    global_scope: ScopeId,
    /// Current scope during building
    current_scope: ScopeId,
    /// All references to symbols in the file
    references: Vec<SymbolReference>,
}

impl SymbolTable {
    /// Create a new symbol table
    pub fn new() -> Self {
        let global_scope = Scope {
            parent: None,
            symbols: HashMap::new(),
            span: Span::new(0, 0),
        };

        Self {
            scopes: vec![global_scope],
            global_scope: 0,
            current_scope: 0,
            references: Vec::new(),
        }
    }

    /// Build symbol table from a source file
    pub fn build(file: &SourceFile, source: &str) -> Self {
        let mut table = Self::new();

        // Collect top-level items
        for item in &file.items {
            table.collect_item(item, file, source);
        }

        table
    }

    /// Collect symbols from an item
    fn collect_item(&mut self, item: &Item, file: &SourceFile, source: &str) {
        match item {
            Item::Function(func) => {
                // Extract doc comments
                let doc = extract_doc_comment(source, func.span.start as usize);

                let symbol = Symbol {
                    name: func.name.clone(),
                    kind: SymbolKind::Function,
                    definition_span: func.span,
                    doc,
                };
                self.define_symbol(symbol);

                // Enter function scope
                self.enter_scope(func.body.span);

                // Define function parameters as symbols in function scope
                for param in &func.params {
                    let param_symbol = Symbol {
                        name: param.name.clone(),
                        kind: SymbolKind::Parameter,
                        definition_span: param.span,
                        doc: None,
                    };
                    self.define_symbol(param_symbol);
                }

                // Collect references and local variables from function body
                self.collect_block_references(&func.body, file);

                // Exit function scope
                self.exit_scope();
            }
            Item::AdaptiveFunction(func) => {
                // Extract doc comments
                let doc = extract_doc_comment(source, func.span.start as usize);

                let symbol = Symbol {
                    name: func.name.clone(),
                    kind: SymbolKind::AdaptiveFunction,
                    definition_span: func.span,
                    doc,
                };
                self.define_symbol(symbol);

                // Each solution is a separate scope
                for solution in &func.solutions {
                    self.enter_scope(solution.body.span);

                    // Define function parameters in each solution scope
                    for param in &func.params {
                        let param_symbol = Symbol {
                            name: param.name.clone(),
                            kind: SymbolKind::Parameter,
                            definition_span: param.span,
                            doc: None,
                        };
                        self.define_symbol(param_symbol);
                    }

                    self.collect_block_references(&solution.body, file);
                    self.exit_scope();
                }
            }
            Item::TypeDef(typedef) => {
                // Extract doc comments
                let doc = extract_doc_comment(source, typedef.span.start as usize);

                let symbol = Symbol {
                    name: typedef.name.clone(),
                    kind: SymbolKind::TypeDef,
                    definition_span: typedef.span,
                    doc,
                };
                self.define_symbol(symbol);
            }
            Item::Const(const_def) => {
                // Extract doc comments
                let doc = extract_doc_comment(source, const_def.span.start as usize);

                let symbol = Symbol {
                    name: const_def.name.clone(),
                    kind: SymbolKind::Const,
                    definition_span: const_def.span,
                    doc,
                };
                self.define_symbol(symbol);
            }
            Item::Import(import) => {
                // Register the imported name (last segment or alias)
                let name = import
                    .alias
                    .clone()
                    .unwrap_or_else(|| import.path.last().cloned().unwrap_or_default());
                if !name.is_empty() {
                    let symbol = Symbol {
                        name,
                        kind: SymbolKind::Variable,
                        definition_span: import.span,
                        doc: None,
                    };
                    self.define_symbol(symbol);
                    // Add references for each path segment
                    for segment in &import.path {
                        self.references.push(SymbolReference {
                            name: segment.clone(),
                            span: import.span,
                            kind: ReferenceKind::Read,
                        });
                    }
                }
            }
            Item::TraitDecl(trait_decl) => {
                let doc = extract_doc_comment(source, trait_decl.span.start as usize);
                let symbol = Symbol {
                    name: trait_decl.name.clone(),
                    kind: SymbolKind::Trait,
                    definition_span: trait_decl.span,
                    doc,
                };
                self.define_symbol(symbol);

                // Enter trait scope and index trait methods
                self.enter_scope(trait_decl.span);
                for item in &trait_decl.items {
                    match item {
                        eclexia_ast::TraitItem::Method { sig, body, .. } => {
                            let method_doc = extract_doc_comment(source, sig.span.start as usize);
                            let method_sym = Symbol {
                                name: sig.name.clone(),
                                kind: SymbolKind::Method,
                                definition_span: sig.span,
                                doc: method_doc,
                            };
                            self.define_symbol(method_sym);
                            if let Some(body) = body {
                                self.enter_scope(body.span);
                                for param in &sig.params {
                                    self.define_symbol(Symbol {
                                        name: param.name.clone(),
                                        kind: SymbolKind::Parameter,
                                        definition_span: param.span,
                                        doc: None,
                                    });
                                }
                                self.collect_block_references(body, file);
                                self.exit_scope();
                            }
                        }
                        eclexia_ast::TraitItem::AssocType { name, span, .. } => {
                            self.define_symbol(Symbol {
                                name: name.clone(),
                                kind: SymbolKind::TypeDef,
                                definition_span: *span,
                                doc: None,
                            });
                        }
                        eclexia_ast::TraitItem::AssocConst { name, span, .. } => {
                            self.define_symbol(Symbol {
                                name: name.clone(),
                                kind: SymbolKind::Const,
                                definition_span: *span,
                                doc: None,
                            });
                        }
                    }
                }
                self.exit_scope();
            }
            Item::ImplBlock(impl_block) => {
                // Enter impl scope and index all methods/assoc items
                self.enter_scope(impl_block.span);
                for item in &impl_block.items {
                    match item {
                        ImplItem::Method { sig, body, .. } => {
                            let method_doc = extract_doc_comment(source, sig.span.start as usize);
                            let method_sym = Symbol {
                                name: sig.name.clone(),
                                kind: SymbolKind::Method,
                                definition_span: sig.span,
                                doc: method_doc,
                            };
                            self.define_symbol(method_sym);

                            // Enter method body scope
                            self.enter_scope(body.span);
                            for param in &sig.params {
                                self.define_symbol(Symbol {
                                    name: param.name.clone(),
                                    kind: SymbolKind::Parameter,
                                    definition_span: param.span,
                                    doc: None,
                                });
                            }
                            self.collect_block_references(body, file);
                            self.exit_scope();
                        }
                        ImplItem::AssocType { span, name, .. } => {
                            self.define_symbol(Symbol {
                                name: name.clone(),
                                kind: SymbolKind::TypeDef,
                                definition_span: *span,
                                doc: None,
                            });
                        }
                        ImplItem::AssocConst { span, name, .. } => {
                            self.define_symbol(Symbol {
                                name: name.clone(),
                                kind: SymbolKind::Const,
                                definition_span: *span,
                                doc: None,
                            });
                        }
                    }
                }
                self.exit_scope();
            }
            Item::ModuleDecl(module_decl) => {
                let doc = extract_doc_comment(source, module_decl.span.start as usize);
                let symbol = Symbol {
                    name: module_decl.name.clone(),
                    kind: SymbolKind::Module,
                    definition_span: module_decl.span,
                    doc,
                };
                self.define_symbol(symbol);

                // If inline module, enter scope and process items
                if let Some(items) = &module_decl.items {
                    self.enter_scope(module_decl.span);
                    for item in items {
                        self.collect_item(item, file, source);
                    }
                    self.exit_scope();
                }
            }
            Item::EffectDecl(effect_decl) => {
                let doc = extract_doc_comment(source, effect_decl.span.start as usize);
                let symbol = Symbol {
                    name: effect_decl.name.clone(),
                    kind: SymbolKind::Effect,
                    definition_span: effect_decl.span,
                    doc,
                };
                self.define_symbol(symbol);

                // Index effect operations as methods
                self.enter_scope(effect_decl.span);
                for op in &effect_decl.operations {
                    self.define_symbol(Symbol {
                        name: op.name.clone(),
                        kind: SymbolKind::Method,
                        definition_span: op.span,
                        doc: None,
                    });
                }
                self.exit_scope();
            }
            Item::StaticDecl(static_decl) => {
                let doc = extract_doc_comment(source, static_decl.span.start as usize);
                let symbol = Symbol {
                    name: static_decl.name.clone(),
                    kind: SymbolKind::Static,
                    definition_span: static_decl.span,
                    doc,
                };
                self.define_symbol(symbol);
            }
            Item::ExternBlock(extern_block) => {
                // Index extern function signatures and statics
                for item in &extern_block.items {
                    match item {
                        ExternItem::Fn(sig) => {
                            let fn_doc = extract_doc_comment(source, sig.span.start as usize);
                            self.define_symbol(Symbol {
                                name: sig.name.clone(),
                                kind: SymbolKind::Function,
                                definition_span: sig.span,
                                doc: fn_doc,
                            });
                        }
                        ExternItem::Static { span, name, .. } => {
                            self.define_symbol(Symbol {
                                name: name.clone(),
                                kind: SymbolKind::Static,
                                definition_span: *span,
                                doc: None,
                            });
                        }
                    }
                }
            }
            Item::Error(_) => {} // Skip error items silently
            Item::MacroDef(m) => {
                let doc = extract_doc_comment(source, m.span.start as usize);
                self.define_symbol(Symbol {
                    name: m.name.clone(),
                    kind: SymbolKind::Function, // macros appear as function-like symbols
                    definition_span: m.span,
                    doc,
                });
            }
        }
    }

    /// Define a symbol in the current scope
    fn define_symbol(&mut self, symbol: Symbol) {
        let name = symbol.name.clone();
        self.scopes[self.current_scope].symbols.insert(name, symbol);
    }

    /// Enter a new scope
    fn enter_scope(&mut self, span: Span) -> ScopeId {
        let scope_id = self.scopes.len();
        let scope = Scope {
            parent: Some(self.current_scope),
            symbols: HashMap::new(),
            span,
        };
        self.scopes.push(scope);
        self.current_scope = scope_id;
        scope_id
    }

    /// Exit the current scope
    fn exit_scope(&mut self) {
        if let Some(parent) = self.scopes[self.current_scope].parent {
            self.current_scope = parent;
        }
    }

    /// Lookup a symbol by name, searching up the scope chain
    pub fn lookup(&self, name: &Ident) -> Option<&Symbol> {
        let mut scope_id = self.current_scope;
        loop {
            if let Some(symbol) = self.scopes[scope_id].symbols.get(name) {
                return Some(symbol);
            }

            if let Some(parent) = self.scopes[scope_id].parent {
                scope_id = parent;
            } else {
                return None;
            }
        }
    }

    /// Get all symbols in the global scope (for document outline)
    pub fn global_symbols(&self) -> Vec<&Symbol> {
        self.scopes[self.global_scope].symbols.values().collect()
    }

    /// Get all symbols in all scopes (for find-all functionality)
    pub fn all_symbols(&self) -> Vec<&Symbol> {
        self.scopes
            .iter()
            .flat_map(|scope| scope.symbols.values())
            .collect()
    }

    /// Collect references from a block
    fn collect_block_references(&mut self, block: &Block, file: &SourceFile) {
        for &stmt_id in &block.stmts {
            self.collect_stmt_references(stmt_id, file);
        }
        if let Some(expr_id) = block.expr {
            self.collect_expr_references(expr_id, file);
        }
    }

    /// Collect references from a statement
    fn collect_stmt_references(&mut self, stmt_id: StmtId, file: &SourceFile) {
        let stmt = &file.stmts[stmt_id];
        match &stmt.kind {
            StmtKind::Let { pattern, value, .. } => {
                // Define all variables bound by the pattern
                self.collect_pattern_bindings(pattern, stmt.span);

                // Collect references from the value expression
                self.collect_expr_references(*value, file);
            }
            StmtKind::Expr(expr_id) => {
                self.collect_expr_references(*expr_id, file);
            }
            StmtKind::Return(Some(expr_id)) => {
                self.collect_expr_references(*expr_id, file);
            }
            StmtKind::Return(None) => {}
            StmtKind::While { condition, body } => {
                self.collect_expr_references(*condition, file);
                self.collect_block_references(body, file);
            }
            StmtKind::For {
                pattern,
                iter,
                body,
            } => {
                // Enter for-loop scope
                self.enter_scope(body.span);

                // Define all variables bound by the pattern in for-loop scope
                self.collect_pattern_bindings(pattern, stmt.span);

                // Collect references from iterator and body
                self.collect_expr_references(*iter, file);
                self.collect_block_references(body, file);

                // Exit for-loop scope
                self.exit_scope();
            }
            StmtKind::Assign { target, value } => {
                // Collect references from target expression (field/index/var)
                self.collect_expr_references(*target, file);
                // Collect references from the value expression
                self.collect_expr_references(*value, file);
            }
            StmtKind::Loop { body, .. } => {
                self.enter_scope(body.span);
                self.collect_block_references(body, file);
                self.exit_scope();
            }
            StmtKind::Break { value, .. } => {
                if let Some(expr_id) = value {
                    self.collect_expr_references(*expr_id, file);
                }
            }
            StmtKind::Continue { .. } => {}
            StmtKind::Error => {} // Skip error statements silently
        }
    }

    /// Collect references from an expression
    fn collect_expr_references(&mut self, expr_id: ExprId, file: &SourceFile) {
        let expr = &file.exprs[expr_id];
        match &expr.kind {
            ExprKind::Var(name) => {
                self.references.push(SymbolReference {
                    name: name.clone(),
                    span: expr.span,
                    kind: ReferenceKind::Read,
                });
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.collect_expr_references(*lhs, file);
                self.collect_expr_references(*rhs, file);
            }
            ExprKind::Unary { operand, .. } => {
                self.collect_expr_references(*operand, file);
            }
            ExprKind::Call { func, args } => {
                self.collect_expr_references(*func, file);
                for &arg in args {
                    self.collect_expr_references(arg, file);
                }
            }
            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                self.collect_expr_references(*receiver, file);
                // Add reference to the method name
                self.references.push(SymbolReference {
                    name: method.clone(),
                    span: expr.span,
                    kind: ReferenceKind::Call,
                });
                for &arg in args {
                    self.collect_expr_references(arg, file);
                }
            }
            ExprKind::Field { expr: inner, field } => {
                self.collect_expr_references(*inner, file);
                // Add reference to the field name
                self.references.push(SymbolReference {
                    name: field.clone(),
                    span: expr.span,
                    kind: ReferenceKind::Read,
                });
            }
            ExprKind::Index { expr, index } => {
                self.collect_expr_references(*expr, file);
                self.collect_expr_references(*index, file);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.collect_expr_references(*condition, file);
                self.collect_block_references(then_branch, file);
                if let Some(else_block) = else_branch {
                    self.collect_block_references(else_block, file);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.collect_expr_references(*scrutinee, file);
                for arm in arms {
                    // Each arm gets its own scope for pattern bindings
                    self.enter_scope(expr.span);
                    self.collect_pattern_bindings(&arm.pattern, expr.span);
                    if let Some(guard) = arm.guard {
                        self.collect_expr_references(guard, file);
                    }
                    self.collect_expr_references(arm.body, file);
                    self.exit_scope();
                }
            }
            ExprKind::Block(block) => {
                self.collect_block_references(block, file);
            }
            ExprKind::Lambda { params, body } => {
                self.enter_scope(expr.span);
                for param in params {
                    self.define_symbol(Symbol {
                        name: param.name.clone(),
                        kind: SymbolKind::Parameter,
                        definition_span: param.span,
                        doc: None,
                    });
                }
                self.collect_expr_references(*body, file);
                self.exit_scope();
            }
            ExprKind::Tuple(exprs) | ExprKind::Array(exprs) => {
                for &e in exprs {
                    self.collect_expr_references(e, file);
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, expr) in fields {
                    self.collect_expr_references(*expr, file);
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                self.collect_expr_references(*value, file);
                self.collect_expr_references(*count, file);
            }
            ExprKind::Try(expr_id) | ExprKind::Deref(expr_id) | ExprKind::Await(expr_id) => {
                self.collect_expr_references(*expr_id, file);
            }
            ExprKind::Borrow { expr, .. } => {
                self.collect_expr_references(*expr, file);
            }
            ExprKind::AsyncBlock(block) => {
                self.collect_block_references(block, file);
            }
            ExprKind::Handle { expr, handlers } => {
                self.collect_expr_references(*expr, file);
                for handler in handlers {
                    self.collect_block_references(&handler.body, file);
                }
            }
            ExprKind::ReturnExpr(opt_expr) => {
                if let Some(expr_id) = opt_expr {
                    self.collect_expr_references(*expr_id, file);
                }
            }
            ExprKind::BreakExpr { value, .. } => {
                if let Some(expr_id) = value {
                    self.collect_expr_references(*expr_id, file);
                }
            }
            ExprKind::ContinueExpr { .. } => {}
            ExprKind::PathExpr(segments) => {
                // Add references for each path segment
                for segment in segments {
                    self.references.push(SymbolReference {
                        name: segment.clone(),
                        span: expr.span,
                        kind: ReferenceKind::Read,
                    });
                }
            }
            ExprKind::Cast { expr: inner, .. } => {
                self.collect_expr_references(*inner, file);
            }
            _ => {} // Literals, errors
        }
    }

    /// Collect all variable bindings from a pattern
    fn collect_pattern_bindings(&mut self, pattern: &Pattern, span: Span) {
        match pattern {
            Pattern::Var(name) => {
                self.define_symbol(Symbol {
                    name: name.clone(),
                    kind: SymbolKind::Variable,
                    definition_span: span,
                    doc: None,
                });
            }
            Pattern::Tuple(pats) | Pattern::Slice(pats) | Pattern::Or(pats) => {
                for pat in pats {
                    self.collect_pattern_bindings(pat, span);
                }
            }
            Pattern::Constructor { name, fields } => {
                // Add reference to the constructor name
                self.references.push(SymbolReference {
                    name: name.clone(),
                    span,
                    kind: ReferenceKind::Read,
                });
                for field in fields {
                    self.collect_pattern_bindings(field, span);
                }
            }
            Pattern::Struct { name, fields, .. } => {
                // Add reference to the struct type name
                self.references.push(SymbolReference {
                    name: name.clone(),
                    span,
                    kind: ReferenceKind::Read,
                });
                for field_pat in fields {
                    if let Some(ref pat) = field_pat.pattern {
                        self.collect_pattern_bindings(pat, span);
                    } else {
                        // Shorthand: `Point { x, y }` binds x and y as variables
                        self.define_symbol(Symbol {
                            name: field_pat.name.clone(),
                            kind: SymbolKind::Variable,
                            definition_span: field_pat.span,
                            doc: None,
                        });
                    }
                }
            }
            Pattern::Binding {
                name,
                pattern: inner,
            } => {
                // name @ pattern -- bind name and recurse into the inner pattern
                self.define_symbol(Symbol {
                    name: name.clone(),
                    kind: SymbolKind::Variable,
                    definition_span: span,
                    doc: None,
                });
                self.collect_pattern_bindings(inner, span);
            }
            Pattern::Range { start, end, .. } => {
                if let Some(pat) = start {
                    self.collect_pattern_bindings(pat, span);
                }
                if let Some(pat) = end {
                    self.collect_pattern_bindings(pat, span);
                }
            }
            Pattern::Reference { pattern: inner, .. } => {
                self.collect_pattern_bindings(inner, span);
            }
            // Wildcard, Literal, Rest don't bind names
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Rest => {}
        }
    }

    /// Find the symbol at a given position
    pub fn symbol_at_position(&self, position: Span) -> Option<&Symbol> {
        // Check if position is in a reference
        for reference in &self.references {
            if reference.span.contains(position.start) {
                // Look up the symbol
                return self.lookup(&reference.name);
            }
        }

        // Check if position is in a symbol definition
        self.all_symbols()
            .into_iter()
            .find(|&symbol| symbol.definition_span.contains(position.start))
            .map(|v| v as _)
    }

    /// Find all references to a symbol
    pub fn find_references(&self, symbol: &Symbol) -> Vec<Span> {
        self.references
            .iter()
            .filter(|r| r.name == symbol.name)
            .map(|r| r.span)
            .collect()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract doc comments by scanning backwards from the definition position.
/// Looks for lines starting with `///` or `//!` immediately before the item.
fn extract_doc_comment(source: &str, def_start: usize) -> Option<String> {
    let bytes = source.as_bytes();
    if def_start == 0 {
        return None;
    }

    // Find the line start before def_start
    let mut line_start = def_start;
    while line_start > 0 && bytes[line_start - 1] != b'\n' {
        line_start -= 1;
    }

    // Scan backwards to collect doc comment lines
    let mut doc_lines = Vec::new();
    let mut current = line_start;

    while current > 0 {
        // Move to previous line
        current = current.saturating_sub(1);
        while current > 0 && bytes[current - 1] != b'\n' {
            current -= 1;
        }

        // Extract the line
        let line_end = if let Some(pos) = bytes[current..].iter().position(|&b| b == b'\n') {
            current + pos
        } else {
            bytes.len()
        };

        let line = std::str::from_utf8(&bytes[current..line_end]).ok()?.trim();

        // Check if it's a doc comment
        if line.starts_with("///") {
            let content = line.trim_start_matches("///").trim();
            doc_lines.push(content.to_string());
        } else if line.starts_with("//!") {
            let content = line.trim_start_matches("//!").trim();
            doc_lines.push(content.to_string());
        } else if line.is_empty() {
            // Empty lines are okay, continue
            continue;
        } else {
            // Not a doc comment line, stop
            break;
        }
    }

    if doc_lines.is_empty() {
        None
    } else {
        // Reverse to get correct order
        doc_lines.reverse();
        Some(doc_lines.join("\n"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smol_str::SmolStr;

    #[test]
    fn test_symbol_table_creation() {
        let table = SymbolTable::new();
        assert_eq!(table.global_symbols().len(), 0);
    }

    #[test]
    fn test_symbol_definition() {
        let mut table = SymbolTable::new();
        let symbol = Symbol {
            name: SmolStr::new("test"),
            kind: SymbolKind::Function,
            definition_span: Span::new(0, 10),
            doc: None,
        };
        table.define_symbol(symbol);

        let lookup = table.lookup(&SmolStr::new("test"));
        assert!(lookup.is_some());
        assert_eq!(lookup.unwrap().kind, SymbolKind::Function);
    }

    #[test]
    fn test_scope_nesting() {
        let mut table = SymbolTable::new();

        // Define in global scope
        table.define_symbol(Symbol {
            name: SmolStr::new("global"),
            kind: SymbolKind::Function,
            definition_span: Span::new(0, 10),
            doc: None,
        });

        // Enter nested scope
        table.enter_scope(Span::new(10, 20));
        table.define_symbol(Symbol {
            name: SmolStr::new("local"),
            kind: SymbolKind::Variable,
            definition_span: Span::new(15, 20),
            doc: None,
        });

        // Both symbols should be visible
        assert!(table.lookup(&SmolStr::new("global")).is_some());
        assert!(table.lookup(&SmolStr::new("local")).is_some());

        // Exit scope
        table.exit_scope();

        // Only global should be visible
        assert!(table.lookup(&SmolStr::new("global")).is_some());
        assert!(table.lookup(&SmolStr::new("local")).is_none());
    }
}
