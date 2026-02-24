// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Eclexia Language Server Protocol implementation.
//!
//! This crate provides LSP server functionality for Eclexia, enabling IDE
//! integration with features like:
//!
//! - Syntax error reporting (parser + type checker + linter diagnostics)
//! - Code completion (keywords + symbols with prefix filtering)
//! - Go-to-definition (symbol table lookup)
//! - Find references (cross-reference tracking)
//! - Document symbols (full outline with all item kinds)
//! - Hover information (symbol kind, name, doc comments)
//! - Rename refactoring (definition + all references)
//! - Signature help (function parameters with types)
//! - Code formatting (via eclexia-fmt)

pub mod server;
pub mod symbols;
