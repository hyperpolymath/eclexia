// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type unification implementation.
//!
//! Implements Robinson's unification algorithm with occurs check.

use crate::{TypeChecker, TypeError};
use eclexia_ast::span::Span;
use eclexia_ast::types::{Ty, TypeVar};

impl TypeChecker<'_> {
    /// Occurs check: does type variable `v` occur in type `t`?
    ///
    /// This prevents infinite types like `a = List<a>`.
    pub fn occurs_check(&self, v: TypeVar, t: &Ty) -> bool {
        let t = self.apply(t);
        match t {
            Ty::Var(v2) => v == v2,
            Ty::Named { args, .. } => args.iter().any(|arg| self.occurs_check(v, arg)),
            Ty::Function { params, ret } => {
                params.iter().any(|p| self.occurs_check(v, p)) || self.occurs_check(v, &ret)
            }
            Ty::Tuple(elems) => elems.iter().any(|e| self.occurs_check(v, e)),
            Ty::Array { elem, .. } => self.occurs_check(v, &elem),
            Ty::ForAll { body, .. } => self.occurs_check(v, &body),
            _ => false,
        }
    }

    /// Unify two types with occurs check
    pub fn unify_with_occurs_check(
        &mut self,
        t1: &Ty,
        t2: &Ty,
        span: Span,
    ) -> Result<(), TypeError> {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);

        if t1 == t2 {
            return Ok(());
        }

        match (&t1, &t2) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),

            (Ty::Var(v), t) | (t, Ty::Var(v)) => {
                // Occurs check
                if self.occurs_check(*v, t) {
                    return Err(TypeError::InfiniteType {
                        span,
                        var: *v,
                        ty: t.clone(),
                        hint: Some(
                            "this type refers to itself infinitely; check your type definitions"
                                .to_string(),
                        ),
                    });
                }

                self.substitution.insert(*v, t.clone());
                Ok(())
            }

            (Ty::Primitive(p1), Ty::Primitive(p2)) => {
                use eclexia_ast::types::PrimitiveTy::*;
                if p1 == p2
                    || matches!(
                        (p1, p2),
                        (Float, F64) | (F64, Float) | (Int, I64) | (I64, Int)
                    )
                {
                    Ok(())
                } else {
                    Err(TypeError::Mismatch {
                        span,
                        expected: t1,
                        found: t2,
                        hint: None,
                    })
                }
            }

            (
                Ty::Function {
                    params: p1,
                    ret: r1,
                },
                Ty::Function {
                    params: p2,
                    ret: r2,
                },
            ) => {
                if p1.len() != p2.len() {
                    return Err(TypeError::Mismatch {
                        span,
                        expected: t1,
                        found: t2,
                        hint: None,
                    });
                }
                for (a, b) in p1.iter().zip(p2.iter()) {
                    self.unify_with_occurs_check(a, b, span)?;
                }
                self.unify_with_occurs_check(r1, r2, span)
            }

            (Ty::Tuple(e1), Ty::Tuple(e2)) => {
                if e1.len() != e2.len() {
                    return Err(TypeError::Mismatch {
                        span,
                        expected: t1,
                        found: t2,
                        hint: None,
                    });
                }
                for (a, b) in e1.iter().zip(e2.iter()) {
                    self.unify_with_occurs_check(a, b, span)?;
                }
                Ok(())
            }

            (Ty::Array { elem: e1, .. }, Ty::Array { elem: e2, .. }) => {
                self.unify_with_occurs_check(e1, e2, span)
            }

            (Ty::Named { name: n1, args: a1 }, Ty::Named { name: n2, args: a2 }) if n1 == n2 => {
                if a1.len() != a2.len() {
                    return Err(TypeError::Mismatch {
                        span,
                        expected: t1,
                        found: t2,
                        hint: None,
                    });
                }
                for (a, b) in a1.iter().zip(a2.iter()) {
                    self.unify_with_occurs_check(a, b, span)?;
                }
                Ok(())
            }

            (
                Ty::Resource {
                    base: b1,
                    dimension: d1,
                },
                Ty::Resource {
                    base: b2,
                    dimension: d2,
                },
            ) => {
                if d1 != d2 {
                    return Err(TypeError::DimensionMismatch {
                        span,
                        dim1: d1.to_string(),
                        dim2: d2.to_string(),
                        hint: Some("resources must have compatible dimensions".to_string()),
                    });
                }
                if b1 != b2 {
                    return Err(TypeError::Mismatch {
                        span,
                        expected: t1,
                        found: t2,
                        hint: None,
                    });
                }
                Ok(())
            }

            _ => Err(TypeError::Mismatch {
                span,
                expected: t1,
                found: t2,
                hint: None,
            }),
        }
    }
}
