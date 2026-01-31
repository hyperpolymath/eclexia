// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Symbol resolution and scope tracking for LSP features.

use eclexia_ast::{Ident, Item, SourceFile, ExprId, StmtId, ExprKind, StmtKind, Block};
use eclexia_ast::span::Span;
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
}

/// A scope containing symbol bindings
#[derive(Debug)]
pub struct Scope {
    /// Parent scope (None for global scope)
    parent: Option<ScopeId>,
    /// Symbols defined in this scope
    symbols: HashMap<Ident, Symbol>,
    /// Span of this scope
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
    pub fn build(file: &SourceFile) -> Self {
        let mut table = Self::new();

        // Collect top-level items
        for item in &file.items {
            table.collect_item(item, file);
        }

        table
    }

    /// Collect symbols from an item
    fn collect_item(&mut self, item: &Item, file: &SourceFile) {
        match item {
            Item::Function(func) => {
                let symbol = Symbol {
                    name: func.name.clone(),
                    kind: SymbolKind::Function,
                    definition_span: func.span,
                    doc: None, // TODO: Extract doc comments
                };
                self.define_symbol(symbol);

                // Collect references from function body
                self.collect_block_references(&func.body, file);
            }
            Item::AdaptiveFunction(func) => {
                let symbol = Symbol {
                    name: func.name.clone(),
                    kind: SymbolKind::AdaptiveFunction,
                    definition_span: func.span,
                    doc: None,
                };
                self.define_symbol(symbol);

                // Collect references from solutions
                for solution in &func.solutions {
                    self.collect_block_references(&solution.body, file);
                }
            }
            Item::TypeDef(typedef) => {
                let symbol = Symbol {
                    name: typedef.name.clone(),
                    kind: SymbolKind::TypeDef,
                    definition_span: typedef.span,
                    doc: None,
                };
                self.define_symbol(symbol);
            }
            Item::Const(const_def) => {
                let symbol = Symbol {
                    name: const_def.name.clone(),
                    kind: SymbolKind::Const,
                    definition_span: const_def.span,
                    doc: None,
                };
                self.define_symbol(symbol);
            }
            Item::Import(_) => {
                // TODO: Handle imports
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
        self.scopes[self.global_scope]
            .symbols
            .values()
            .collect()
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
            StmtKind::Let { value, .. } => {
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
            StmtKind::For { iter, body, .. } => {
                self.collect_expr_references(*iter, file);
                self.collect_block_references(body, file);
            }
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
            ExprKind::MethodCall { receiver, args, .. } => {
                self.collect_expr_references(*receiver, file);
                for &arg in args {
                    self.collect_expr_references(arg, file);
                }
            }
            ExprKind::Field { expr, .. } => {
                self.collect_expr_references(*expr, file);
            }
            ExprKind::Index { expr, index } => {
                self.collect_expr_references(*expr, file);
                self.collect_expr_references(*index, file);
            }
            ExprKind::If { condition, then_branch, else_branch } => {
                self.collect_expr_references(*condition, file);
                self.collect_block_references(then_branch, file);
                if let Some(else_block) = else_branch {
                    self.collect_block_references(else_block, file);
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                self.collect_expr_references(*scrutinee, file);
                for arm in arms {
                    self.collect_expr_references(arm.body, file);
                    if let Some(guard) = arm.guard {
                        self.collect_expr_references(guard, file);
                    }
                }
            }
            ExprKind::Block(block) => {
                self.collect_block_references(block, file);
            }
            ExprKind::Lambda { body, .. } => {
                self.collect_expr_references(*body, file);
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
            _ => {} // Literals, errors, etc.
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
        for symbol in self.all_symbols() {
            if symbol.definition_span.contains(position.start) {
                return Some(symbol);
            }
        }

        None
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
