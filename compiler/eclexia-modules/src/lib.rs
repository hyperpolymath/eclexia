// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Module system for the Eclexia compiler.
//!
//! Provides:
//! - Module resolution (mapping import paths to file paths)
//! - Interface files (`.ecli`) for separate compilation
//! - Dependency graph construction and topological ordering
//!
//! # Module Resolution
//!
//! Eclexia uses a file-based module system where each `.ecl` file
//! is a module. Import paths map to file paths relative to the
//! project root:
//!
//! ```text
//! import std.collections.hashmap  →  std/collections/hashmap.ecl
//! import my_module                →  my_module.ecl
//! import sub.nested               →  sub/nested.ecl
//! ```
//!
//! # Interface Files
//!
//! When a module is compiled, its public API is serialized to a
//! `.ecli` (Eclexia Interface) file. This enables separate compilation:
//! downstream modules only need the interface, not the full source.
//!
//! # Dependency Graph
//!
//! The dependency graph tracks which modules depend on which others.
//! It supports:
//! - Topological ordering for compilation scheduling
//! - Reverse dependency lookup for incremental recompilation
//! - Cycle detection

pub mod interface;
pub mod dep_graph;
pub mod parallel;

use std::path::{Path, PathBuf};

use eclexia_ast::SourceFile;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use thiserror::Error;

/// Unique identifier for a module within a project.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleId {
    /// Dot-separated module path (e.g., "std.collections.hashmap").
    pub path: SmolStr,
}

impl ModuleId {
    pub fn new(path: impl Into<SmolStr>) -> Self {
        Self { path: path.into() }
    }

    /// Convert module path to a file system path relative to the project root.
    pub fn to_file_path(&self) -> PathBuf {
        let mut path = PathBuf::new();
        for segment in self.path.split('.') {
            path.push(segment);
        }
        path.set_extension("ecl");
        path
    }

    /// Create a ModuleId from a file path relative to the project root.
    pub fn from_file_path(path: &Path) -> Option<Self> {
        let stem = path.with_extension("");
        let components: Vec<_> = stem
            .components()
            .filter_map(|c| c.as_os_str().to_str())
            .collect();

        if components.is_empty() {
            return None;
        }

        Some(Self {
            path: SmolStr::new(components.join(".")),
        })
    }
}

impl std::fmt::Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path)
    }
}

/// Module resolution errors.
#[derive(Debug, Error)]
pub enum ModuleError {
    #[error("module not found: {module_id}")]
    NotFound { module_id: ModuleId },

    #[error("circular dependency: {cycle:?}")]
    CircularDependency { cycle: Vec<ModuleId> },

    #[error("failed to read module {module_id}: {source}")]
    IoError {
        module_id: ModuleId,
        source: std::io::Error,
    },

    #[error("failed to parse module {module_id}: {message}")]
    ParseError {
        module_id: ModuleId,
        message: String,
    },
}

/// Module resolver that maps import paths to file paths and tracks
/// discovered modules.
pub struct ModuleResolver {
    /// Project root directory.
    root: PathBuf,
    /// Search paths for standard library and packages.
    search_paths: Vec<PathBuf>,
    /// Cached module paths: ModuleId → absolute file path.
    resolved: FxHashMap<ModuleId, PathBuf>,
}

impl ModuleResolver {
    /// Create a new resolver rooted at the given directory.
    pub fn new(root: PathBuf) -> Self {
        Self {
            root,
            search_paths: Vec::new(),
            resolved: FxHashMap::default(),
        }
    }

    /// Add a search path for library/package modules.
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.search_paths.push(path);
    }

    /// Resolve a module import to its file path.
    pub fn resolve(&mut self, module_id: &ModuleId) -> Result<PathBuf, ModuleError> {
        if let Some(path) = self.resolved.get(module_id) {
            return Ok(path.clone());
        }

        let relative = module_id.to_file_path();

        // Check project root first
        let candidate = self.root.join(&relative);
        if candidate.exists() {
            self.resolved.insert(module_id.clone(), candidate.clone());
            return Ok(candidate);
        }

        // Check search paths (stdlib, packages)
        for search in &self.search_paths {
            let candidate = search.join(&relative);
            if candidate.exists() {
                self.resolved.insert(module_id.clone(), candidate.clone());
                return Ok(candidate);
            }
        }

        Err(ModuleError::NotFound {
            module_id: module_id.clone(),
        })
    }

    /// Discover all `.ecl` files in the project and register them.
    pub fn discover_modules(&mut self) -> Result<Vec<ModuleId>, ModuleError> {
        let mut modules = Vec::new();
        self.discover_recursive(&self.root.clone(), &PathBuf::new(), &mut modules)?;
        Ok(modules)
    }

    fn discover_recursive(
        &mut self,
        dir: &Path,
        relative_prefix: &Path,
        modules: &mut Vec<ModuleId>,
    ) -> Result<(), ModuleError> {
        let entries = std::fs::read_dir(dir).map_err(|e| ModuleError::IoError {
            module_id: ModuleId::new("_discovery"),
            source: e,
        })?;

        for entry in entries {
            let entry = entry.map_err(|e| ModuleError::IoError {
                module_id: ModuleId::new("_discovery"),
                source: e,
            })?;
            let path = entry.path();

            if path.is_dir() {
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if name.starts_with('.') || name == "target" {
                        continue;
                    }
                }
                let Some(fname) = path.file_name() else { continue };
                let new_prefix = relative_prefix.join(fname);
                self.discover_recursive(&path, &new_prefix, modules)?;
            } else if path.extension().and_then(|e| e.to_str()) == Some("ecl") {
                let Some(fname) = path.file_name() else { continue };
                let relative = relative_prefix.join(fname);
                if let Some(module_id) = ModuleId::from_file_path(&relative) {
                    self.resolved
                        .insert(module_id.clone(), path.canonicalize().unwrap_or(path));
                    modules.push(module_id);
                }
            }
        }

        Ok(())
    }

    /// Get the resolved path for a module, if already resolved.
    pub fn get_path(&self, module_id: &ModuleId) -> Option<&PathBuf> {
        self.resolved.get(module_id)
    }
}

/// Extract import paths from a parsed source file.
///
/// Scans the AST for `import` items and returns the module IDs
/// they reference.
pub fn extract_imports(file: &SourceFile) -> Vec<ModuleId> {
    let mut imports = Vec::new();

    for item in &file.items {
        if let eclexia_ast::Item::Import(import) = item {
            // Build the module path from the import path segments
            // Ident is SmolStr, so .as_str() works directly
            let path = import
                .path
                .iter()
                .map(|segment| segment.as_str())
                .collect::<Vec<_>>()
                .join(".");

            if !path.is_empty() {
                imports.push(ModuleId::new(path));
            }
        }
    }

    imports
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_id_to_file_path() {
        let id = ModuleId::new("std.collections.hashmap");
        assert_eq!(id.to_file_path(), PathBuf::from("std/collections/hashmap.ecl"));
    }

    #[test]
    fn test_module_id_from_file_path() {
        let path = Path::new("std/collections/hashmap.ecl");
        let id = ModuleId::from_file_path(path).unwrap();
        assert_eq!(id.path.as_str(), "std.collections.hashmap");
    }

    #[test]
    fn test_module_id_simple() {
        let id = ModuleId::new("my_module");
        assert_eq!(id.to_file_path(), PathBuf::from("my_module.ecl"));
    }

    #[test]
    fn test_module_id_display() {
        let id = ModuleId::new("std.io");
        assert_eq!(format!("{}", id), "std.io");
    }
}
