// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type checker for the Eclexia programming language.
//!
//! This crate implements bidirectional type checking with:
//! - Hindley-Milner type inference
//! - Dimensional type checking for resource types
//! - Constraint solving for resource bounds
//! - Effect tracking

mod infer;
mod unify;
mod env;
mod error;

use eclexia_ast::types::{Ty, TypeVar};
use eclexia_ast::SourceFile;
use rustc_hash::FxHashMap;

pub use error::{TypeError, TypeResult};
pub use env::TypeEnv;

/// Type checker state.
pub struct TypeChecker {
    /// Environment with type bindings
    env: TypeEnv,
    /// Substitution from type variables to types
    substitution: FxHashMap<TypeVar, Ty>,
    /// Next type variable ID
    next_var: u32,
    /// Collected errors
    errors: Vec<TypeError>,
}

impl TypeChecker {
    /// Create a new type checker.
    pub fn new() -> Self {
        Self {
            env: TypeEnv::new(),
            substitution: FxHashMap::default(),
            next_var: 0,
            errors: Vec::new(),
        }
    }

    /// Generate a fresh type variable.
    pub fn fresh_var(&mut self) -> Ty {
        let var = TypeVar::new(self.next_var);
        self.next_var += 1;
        Ty::Var(var)
    }

    /// Check a source file.
    pub fn check_file(&mut self, _file: &SourceFile) -> Vec<TypeError> {
        // TODO: Implement type checking
        std::mem::take(&mut self.errors)
    }

    /// Apply the current substitution to a type.
    pub fn apply(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(v) => {
                if let Some(t) = self.substitution.get(v) {
                    self.apply(t)
                } else {
                    ty.clone()
                }
            }
            Ty::Named { name, args } => Ty::Named {
                name: name.clone(),
                args: args.iter().map(|t| self.apply(t)).collect(),
            },
            Ty::Function { params, ret } => Ty::Function {
                params: params.iter().map(|t| self.apply(t)).collect(),
                ret: Box::new(self.apply(ret)),
            },
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|t| self.apply(t)).collect()),
            Ty::Array { elem, size } => Ty::Array {
                elem: Box::new(self.apply(elem)),
                size: *size,
            },
            Ty::ForAll { vars, body } => Ty::ForAll {
                vars: vars.clone(),
                body: Box::new(self.apply(body)),
            },
            _ => ty.clone(),
        }
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

/// Type check a source file.
pub fn check(file: &SourceFile) -> Vec<TypeError> {
    let mut checker = TypeChecker::new();
    checker.check_file(file)
}
