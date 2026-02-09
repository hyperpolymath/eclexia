// SPDX-License-Identifier: PMPL-1.0-or-later
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
    /// Struct field type registry: struct_name -> [(field_name, field_type)]
    pub struct_fields: FxHashMap<SmolStr, Vec<(SmolStr, Ty)>>,
    /// Trait method registry: trait_name -> [(method_name, method_type)]
    pub trait_methods: FxHashMap<SmolStr, Vec<(SmolStr, Ty)>>,
    /// Impl method registry: type_name -> [(method_name, method_type)]
    pub impl_methods: FxHashMap<SmolStr, Vec<(SmolStr, Ty)>>,
}

impl TypeEnv {
    /// Create a new empty environment.
    pub fn new() -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: None,
            struct_fields: FxHashMap::default(),
            trait_methods: FxHashMap::default(),
            impl_methods: FxHashMap::default(),
        }
    }

    /// Create a child environment.
    pub fn child(&self) -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: Some(Box::new(self.clone())),
            struct_fields: FxHashMap::default(),
            trait_methods: FxHashMap::default(),
            impl_methods: FxHashMap::default(),
        }
    }

    /// Register struct fields for field-access type checking.
    pub fn register_struct(&mut self, name: SmolStr, fields: Vec<(SmolStr, Ty)>) {
        self.struct_fields.insert(name, fields);
    }

    /// Register trait methods.
    pub fn register_trait(&mut self, name: SmolStr, methods: Vec<(SmolStr, Ty)>) {
        self.trait_methods.insert(name, methods);
    }

    /// Register impl block methods for a type.
    pub fn register_impl_methods(&mut self, type_name: SmolStr, methods: Vec<(SmolStr, Ty)>) {
        self.impl_methods.entry(type_name).or_default().extend(methods);
    }

    /// Look up a struct field type.
    pub fn lookup_field(&self, struct_name: &str, field_name: &str) -> Option<Ty> {
        if let Some(fields) = self.struct_fields.get(struct_name) {
            for (name, ty) in fields {
                if name.as_str() == field_name {
                    return Some(ty.clone());
                }
            }
        }
        if let Some(parent) = &self.parent {
            return parent.lookup_field(struct_name, field_name);
        }
        None
    }

    /// Look up a method for a type (checks impl blocks, then traits).
    pub fn lookup_method(&self, type_name: &str, method_name: &str) -> Option<Ty> {
        if let Some(methods) = self.impl_methods.get(type_name) {
            for (name, ty) in methods {
                if name.as_str() == method_name {
                    return Some(ty.clone());
                }
            }
        }
        // Check trait methods
        for methods in self.trait_methods.values() {
            for (name, ty) in methods {
                if name.as_str() == method_name {
                    return Some(ty.clone());
                }
            }
        }
        if let Some(parent) = &self.parent {
            return parent.lookup_method(type_name, method_name);
        }
        None
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

    /// Get all available names in this environment and parent environments.
    pub fn available_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.bindings.keys().map(|s| s.to_string()).collect();
        if let Some(parent) = &self.parent {
            names.extend(parent.available_names());
        }
        names
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}
