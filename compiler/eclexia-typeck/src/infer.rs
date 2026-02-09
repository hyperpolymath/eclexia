// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type inference implementation.
//!
//! Implements generalization and instantiation for let-polymorphism.

use crate::{TypeChecker, TypeEnv};
use eclexia_ast::types::{Ty, TypeVar};
use smol_str::SmolStr;
use rustc_hash::FxHashSet;

impl TypeChecker<'_> {
    /// Generalize a type by abstracting free type variables into a ForAll.
    ///
    /// This enables let-polymorphism: `let id = fn(x) { x }` gets type `∀a. a -> a`.
    pub fn generalize(&self, ty: &Ty, env: &TypeEnv) -> Ty {
        let ty = self.apply(ty);
        let free_in_ty = self.free_vars(&ty);
        let free_in_env = env.free_vars();

        // Variables free in type but not in environment can be generalized
        let generalizable: Vec<SmolStr> = free_in_ty
            .difference(&free_in_env)
            .map(|v| SmolStr::new(format!("t{}", v.0)))
            .collect();

        if generalizable.is_empty() {
            ty
        } else {
            Ty::ForAll {
                vars: generalizable,
                body: Box::new(ty),
            }
        }
    }

    /// Instantiate a ForAll type with fresh type variables.
    ///
    /// Turns `∀a. a -> a` into `t100 -> t100` with fresh variable t100.
    pub fn instantiate(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::ForAll { vars, body } => {
                let mut subst = rustc_hash::FxHashMap::default();

                // Create fresh variables for each quantified variable
                for var in vars {
                    let fresh = self.fresh_var();
                    subst.insert(var.clone(), fresh);
                }

                // Apply substitution to body
                self.substitute_vars(body, &subst)
            }
            _ => ty.clone(),
        }
    }

    /// Get free type variables in a type
    fn free_vars(&self, ty: &Ty) -> FxHashSet<TypeVar> {
        let ty = self.apply(ty);
        match ty {
            Ty::Var(v) => {
                let mut set = FxHashSet::default();
                set.insert(v);
                set
            }
            Ty::Named { args, .. } => {
                args.iter().flat_map(|t| self.free_vars(t)).collect()
            }
            Ty::Function { params, ret } => {
                let mut vars: FxHashSet<TypeVar> =
                    params.iter().flat_map(|p| self.free_vars(p)).collect();
                vars.extend(self.free_vars(&ret));
                vars
            }
            Ty::Tuple(elems) => elems.iter().flat_map(|e| self.free_vars(e)).collect(),
            Ty::Array { elem, .. } => self.free_vars(&elem),
            Ty::ForAll { vars, body } => {
                // Variables bound by ForAll are not free
                let mut free = self.free_vars(&body);
                for var in vars {
                    // Remove bound variables (this is simplified - proper implementation
                    // would track variable names more carefully)
                    free.retain(|v| format!("t{}", v.0) != var.as_str());
                }
                free
            }
            Ty::Resource { .. } | Ty::Primitive(_) | Ty::Error | Ty::Never => {
                FxHashSet::default()
            }
        }
    }

    /// Substitute type variables in a type
    fn substitute_vars(
        &self,
        ty: &Ty,
        subst: &rustc_hash::FxHashMap<SmolStr, Ty>,
    ) -> Ty {
        match ty {
            Ty::Var(v) => {
                let name = SmolStr::new(format!("t{}", v.0));
                subst.get(&name).cloned().unwrap_or_else(|| ty.clone())
            }
            Ty::Named { name, args } => Ty::Named {
                name: name.clone(),
                args: args.iter().map(|t| self.substitute_vars(t, subst)).collect(),
            },
            Ty::Function { params, ret } => Ty::Function {
                params: params
                    .iter()
                    .map(|t| self.substitute_vars(t, subst))
                    .collect(),
                ret: Box::new(self.substitute_vars(ret, subst)),
            },
            Ty::Tuple(elems) => Ty::Tuple(
                elems
                    .iter()
                    .map(|t| self.substitute_vars(t, subst))
                    .collect(),
            ),
            Ty::Array { elem, size } => Ty::Array {
                elem: Box::new(self.substitute_vars(elem, subst)),
                size: *size,
            },
            Ty::ForAll { vars, body } => Ty::ForAll {
                vars: vars.clone(),
                body: Box::new(self.substitute_vars(body, subst)),
            },
            _ => ty.clone(),
        }
    }
}

impl TypeEnv {
    /// Get all free type variables in the environment
    pub fn free_vars(&self) -> FxHashSet<TypeVar> {
        // In a real implementation, this would traverse all types in the environment
        // For now, return empty set
        FxHashSet::default()
    }
}
