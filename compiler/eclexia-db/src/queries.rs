// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Salsa tracked query functions wrapping the compiler pipeline.
//!
//! Each function here wraps an existing compiler crate's API as a
//! salsa tracked function. Salsa memoizes the result and tracks
//! which inputs each query reads, so it can skip re-execution
//! when inputs haven't changed.

use std::sync::Arc;

use crate::{
    next_generation, AstWrapper, BytecodeWrapper, Diagnostic, DiagnosticPhase, DiagnosticSeverity,
    HirWrapper, LintDiagnostic, LintSeverity, MirWrapper, ParseError, SourceFile, TypeCheckError,
};

/// Parse a source file into an AST.
///
/// Wraps `eclexia_parser::parse()` as a salsa tracked function.
/// Result is memoized — calling twice with same text returns cached result.
#[salsa::tracked]
pub fn parse(db: &dyn salsa::Database, source: SourceFile) -> (AstWrapper, Vec<ParseError>) {
    let text = source.text(db);
    let (ast, errors) = eclexia_parser::parse(&text);

    let parse_errors: Vec<ParseError> = errors
        .iter()
        .map(|e| {
            let span = e.span();
            ParseError {
                message: format!("{}", e),
                offset: span.start as usize,
                len: (span.end.saturating_sub(span.start)) as usize,
            }
        })
        .collect();

    let wrapper = AstWrapper {
        ast: Arc::new(ast),
        generation: next_generation(),
    };

    (wrapper, parse_errors)
}

/// Type-check a parsed file.
///
/// Depends on `parse()` — salsa tracks this dependency automatically.
#[salsa::tracked]
pub fn type_check(db: &dyn salsa::Database, source: SourceFile) -> Vec<TypeCheckError> {
    let (ast_wrapper, parse_errors) = parse(db, source);

    if !parse_errors.is_empty() {
        return vec![];
    }

    let errors = eclexia_typeck::check(&ast_wrapper.ast);

    errors
        .iter()
        .map(|e| {
            let span = e.span();
            TypeCheckError {
                message: format!("{}", e),
                offset: span.start as usize,
                len: (span.end.saturating_sub(span.start)) as usize,
            }
        })
        .collect()
}

/// Lower AST to HIR (High-level Intermediate Representation).
#[salsa::tracked]
pub fn lower_hir(db: &dyn salsa::Database, source: SourceFile) -> HirWrapper {
    let (ast_wrapper, _errors) = parse(db, source);
    let hir = eclexia_hir::lower_source_file(&ast_wrapper.ast);

    HirWrapper {
        hir: Arc::new(hir),
        generation: next_generation(),
    }
}

/// Lower HIR to MIR (Mid-level Intermediate Representation).
#[salsa::tracked]
pub fn lower_mir(db: &dyn salsa::Database, source: SourceFile) -> MirWrapper {
    let hir_wrapper = lower_hir(db, source);
    let mir = eclexia_mir::lower_hir_file(&hir_wrapper.hir);

    MirWrapper {
        mir: Arc::new(mir),
        generation: next_generation(),
    }
}

/// Generate bytecode from MIR.
#[salsa::tracked]
pub fn generate_bytecode(db: &dyn salsa::Database, source: SourceFile) -> BytecodeWrapper {
    use eclexia_codegen::Backend;

    let mir_wrapper = lower_mir(db, source);

    let mut codegen = eclexia_codegen::BytecodeGenerator::new();
    let module = match codegen.generate(&mir_wrapper.mir) {
        Ok(module) => module,
        Err(e) => {
            tracing::error!("Bytecode generation failed: {}", e);
            eclexia_codegen::BytecodeModule {
                functions: Vec::new(),
                strings: Vec::new(),
                floats: Vec::new(),
                integers: Vec::new(),
                entry_point: None,
            }
        }
    };

    BytecodeWrapper {
        module: Arc::new(module),
        generation: next_generation(),
    }
}

/// Run the linter on a parsed file.
#[salsa::tracked]
pub fn lint(db: &dyn salsa::Database, source: SourceFile) -> Vec<LintDiagnostic> {
    let (ast_wrapper, parse_errors) = parse(db, source);
    let text = source.text(db);

    if !parse_errors.is_empty() {
        return vec![];
    }

    let linter = eclexia_lint::Linter::new();
    let diagnostics = linter.lint(&ast_wrapper.ast, &text);

    diagnostics
        .iter()
        .map(|d| LintDiagnostic {
            message: d.message.clone(),
            severity: match d.severity {
                eclexia_lint::diagnostics::Severity::Warning => LintSeverity::Warning,
                eclexia_lint::diagnostics::Severity::Info => LintSeverity::Info,
                eclexia_lint::diagnostics::Severity::Error => LintSeverity::Warning,
            },
            offset: d.span.start as usize,
            len: (d.span.end.saturating_sub(d.span.start)) as usize,
        })
        .collect()
}

/// Collect all diagnostics for a file across all compiler phases.
///
/// This is the main query used by the LSP and CLI to get a unified
/// view of all errors, warnings, and hints for a file.
#[salsa::tracked]
pub fn all_diagnostics(db: &dyn salsa::Database, source: SourceFile) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    let (_ast_wrapper, parse_errors) = parse(db, source);
    for err in &parse_errors {
        diagnostics.push(Diagnostic {
            phase: DiagnosticPhase::Parse,
            severity: DiagnosticSeverity::Error,
            message: err.message.clone(),
            offset: err.offset,
            len: err.len,
        });
    }

    if parse_errors.is_empty() {
        let type_errors = type_check(db, source);
        for err in &type_errors {
            diagnostics.push(Diagnostic {
                phase: DiagnosticPhase::TypeCheck,
                severity: DiagnosticSeverity::Error,
                message: err.message.clone(),
                offset: err.offset,
                len: err.len,
            });
        }
    }

    let lint_results = lint(db, source);
    for d in &lint_results {
        diagnostics.push(Diagnostic {
            phase: DiagnosticPhase::Lint,
            severity: match d.severity {
                LintSeverity::Warning => DiagnosticSeverity::Warning,
                LintSeverity::Info => DiagnosticSeverity::Info,
                LintSeverity::Hint => DiagnosticSeverity::Hint,
            },
            message: d.message.clone(),
            offset: d.offset,
            len: d.len,
        });
    }

    diagnostics
}
