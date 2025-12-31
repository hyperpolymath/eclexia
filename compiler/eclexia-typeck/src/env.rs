// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type environment for variable bindings.

use eclexia_ast::types::{Ty, TypeScheme};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

/// Type environment mapping names to type schemes.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    bindings: FxHashMap<SmolStr, TypeScheme>,
    parent: Option<Box<TypeEnv>>,
}

impl TypeEnv {
    /// Create a new empty environment.
    pub fn new() -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: None,
        }
    }

    /// Create a child environment.
    pub fn child(&self) -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: Some(Box::new(self.clone())),
        }
    }

    /// Insert a binding.
    pub fn insert(&mut self, name: SmolStr, scheme: TypeScheme) {
        self.bindings.insert(name, scheme);
    }

    /// Look up a binding.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.bindings.get(name).or_else(|| {
            self.parent.as_ref().and_then(|p| p.lookup(name))
        })
    }

    /// Insert a monomorphic type.
    pub fn insert_mono(&mut self, name: SmolStr, ty: Ty) {
        self.insert(name, TypeScheme::mono(ty));
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}
