// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Incremental compilation database for Eclexia.
//!
//! This crate wraps the entire compiler pipeline in a salsa incremental
//! computation framework. Each compilation phase (parse, type-check, HIR
//! lowering, MIR lowering, codegen) becomes a memoized query that
//! automatically re-executes only when its inputs change.
//!
//! The database serves as the single source of truth for:
//! - The CLI driver (`eclexia build`, `eclexia check`, etc.)
//! - The LSP server (incremental re-analysis on keystroke)
//! - Watch mode (file-system driven re-compilation)
//!
//! # Usage
//!
//! ```ignore
//! use eclexia_db::{SourceFile, queries};
//!
//! let mut db = salsa::DatabaseImpl::new();
//! let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());
//!
//! // Parse (memoized)
//! let (ast, errors) = queries::parse(&db, source);
//!
//! // Type check (depends on parse, also memoized)
//! let type_errors = queries::type_check(&db, source);
//!
//! // Update source text — only affected queries re-execute
//! use salsa::Setter;
//! source.set_text(&mut db).to("def main() -> Unit { println(\"updated\") }".to_string());
//! let type_errors = queries::type_check(&db, source); // re-runs parse + type_check
//! ```

pub mod queries;
pub mod vfs;

use std::sync::Arc;

// Re-export salsa for downstream consumers
pub use salsa;

/// The central compiler database type.
///
/// Uses `salsa::DatabaseImpl` which provides built-in Storage management.
/// All compiler queries go through tracked functions that take `&dyn salsa::Database`.
pub type CompilerDatabase = salsa::DatabaseImpl;

/// The source text of a file. This is a salsa *input* — the only
/// mutable entry point into the database.
///
/// When file contents change (via VFS notification or LSP sync),
/// we call `source.set_text(&mut db).to(new_text)` which invalidates
/// all downstream queries that depend on this file's text.
#[salsa::input]
pub struct SourceFile {
    pub text: String,
}

/// Wrapper for parsed AST that implements the traits salsa needs.
/// We use Arc to make cloning cheap and a generation counter for
/// change detection.
#[derive(Clone, Debug)]
pub struct AstWrapper {
    pub ast: Arc<eclexia_ast::SourceFile>,
    generation: u64,
}

impl PartialEq for AstWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation && Arc::ptr_eq(&self.ast, &other.ast)
    }
}

impl Eq for AstWrapper {}

impl std::hash::Hash for AstWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.generation.hash(state);
    }
}

/// Wrapper for HIR that salsa can track.
#[derive(Clone, Debug)]
pub struct HirWrapper {
    pub hir: Arc<eclexia_hir::HirFile>,
    generation: u64,
}

impl PartialEq for HirWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation && Arc::ptr_eq(&self.hir, &other.hir)
    }
}

impl Eq for HirWrapper {}

impl std::hash::Hash for HirWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.generation.hash(state);
    }
}

/// Wrapper for MIR that salsa can track.
#[derive(Clone, Debug)]
pub struct MirWrapper {
    pub mir: Arc<eclexia_mir::MirFile>,
    generation: u64,
}

impl PartialEq for MirWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation && Arc::ptr_eq(&self.mir, &other.mir)
    }
}

impl Eq for MirWrapper {}

impl std::hash::Hash for MirWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.generation.hash(state);
    }
}

/// Wrapper for BytecodeModule that salsa can track.
#[derive(Clone, Debug)]
pub struct BytecodeWrapper {
    pub module: Arc<eclexia_codegen::BytecodeModule>,
    generation: u64,
}

impl PartialEq for BytecodeWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation && Arc::ptr_eq(&self.module, &other.module)
    }
}

impl Eq for BytecodeWrapper {}

impl std::hash::Hash for BytecodeWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.generation.hash(state);
    }
}

/// A parse error with span information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseError {
    pub message: String,
    pub offset: usize,
    pub len: usize,
}

/// A type-check error with span information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeCheckError {
    pub message: String,
    pub offset: usize,
    pub len: usize,
}

/// A lint diagnostic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LintDiagnostic {
    pub message: String,
    pub severity: LintSeverity,
    pub offset: usize,
    pub len: usize,
}

/// Lint severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LintSeverity {
    Warning,
    Info,
    Hint,
}

/// Unified diagnostic type for all compiler phases.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub phase: DiagnosticPhase,
    pub severity: DiagnosticSeverity,
    pub message: String,
    pub offset: usize,
    pub len: usize,
}

/// Which compiler phase produced the diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticPhase {
    Parse,
    TypeCheck,
    Lint,
    Codegen,
}

/// Diagnostic severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

/// Global generation counter for creating unique wrapper IDs.
static GENERATION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Get the next generation number.
pub(crate) fn next_generation() -> u64 {
    GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_through_salsa() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());

        let (ast_wrapper, errors) = queries::parse(&db, source);
        assert!(
            errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            errors
        );
        assert!(
            !ast_wrapper.ast.items.is_empty(),
            "Expected at least one item"
        );
    }

    #[test]
    fn test_type_check_through_salsa() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());

        let type_errors = queries::type_check(&db, source);
        assert!(
            type_errors.is_empty(),
            "Expected no type errors, got: {:?}",
            type_errors
        );
    }

    #[test]
    fn test_all_diagnostics_clean_file() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());

        let diags = queries::all_diagnostics(&db, source);
        // May have lint warnings but should have no errors
        let errors: Vec<_> = diags
            .iter()
            .filter(|d| d.severity == DiagnosticSeverity::Error)
            .collect();
        assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors);
    }

    #[test]
    fn test_parse_error_propagation() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def { broken syntax".to_string());

        let (_ast, errors) = queries::parse(&db, source);
        assert!(
            !errors.is_empty(),
            "Expected parse errors for broken syntax"
        );
    }

    #[test]
    fn test_incremental_reparse() {
        let mut db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"v1\") }".to_string());

        // First parse
        let (ast1, errors1) = queries::parse(&db, source);
        assert!(errors1.is_empty());

        // Update source text
        use salsa::Setter;
        source
            .set_text(&mut db)
            .to("def main() -> Unit { println(\"v2\") }".to_string());

        // Second parse — should produce a different generation
        let (ast2, errors2) = queries::parse(&db, source);
        assert!(errors2.is_empty());
        assert_ne!(
            ast1.generation, ast2.generation,
            "Generation should differ after reparse"
        );
    }

    #[test]
    fn test_hir_lowering() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());

        let hir = queries::lower_hir(&db, source);
        assert!(!hir.hir.items.is_empty(), "Expected at least one HIR item");
    }

    #[test]
    fn test_full_pipeline() {
        let db = CompilerDatabase::new();
        let source = SourceFile::new(&db, "def main() -> Unit { println(\"hello\") }".to_string());

        // Run through the full pipeline — verify each stage completes without panic
        let (_ast, errors) = queries::parse(&db, source);
        assert!(errors.is_empty());

        let type_errors = queries::type_check(&db, source);
        assert!(type_errors.is_empty());

        let hir = queries::lower_hir(&db, source);
        assert!(!hir.hir.items.is_empty(), "Expected at least one HIR item");

        let _mir = queries::lower_mir(&db, source);
        // Bytecode generation completes without error
        let _bytecode = queries::generate_bytecode(&db, source);
    }

    #[test]
    fn test_vfs_load_and_query() {
        let mut db = CompilerDatabase::new();
        let mut vfs = vfs::Vfs::new();

        // Add a file via VFS
        let changes = vfs::ChangeSet::from_file(
            std::path::PathBuf::from("test.ecl"),
            "def greet() -> Unit { println(\"hi\") }".to_string(),
        );
        vfs.apply_changes(&mut db, changes);

        // Query through VFS
        let source = match vfs.get(std::path::Path::new("test.ecl")) {
            Some(src) => src,
            None => panic!("File should be tracked"),
        };
        let (_ast, errors) = queries::parse(&db, source);
        assert!(errors.is_empty());
    }
}
