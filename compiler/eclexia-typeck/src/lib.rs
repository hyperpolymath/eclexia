// SPDX-License-Identifier: PMPL-1.0-or-later
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

use eclexia_ast::types::{Ty, TypeVar, PrimitiveTy};
use eclexia_ast::dimension::Dimension;
use eclexia_ast::{SourceFile, Item, Function, AdaptiveFunction, ExprId, StmtId, ExprKind, StmtKind, BinaryOp, UnaryOp, Literal, Block, Constraint, ConstraintKind, Pattern};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

pub use error::{TypeError, TypeResult};
pub use env::TypeEnv;

/// Type checker state.
pub struct TypeChecker<'a> {
    /// The source file being checked
    file: &'a SourceFile,
    /// Environment with type bindings
    env: TypeEnv,
    /// Substitution from type variables to types
    substitution: FxHashMap<TypeVar, Ty>,
    /// Next type variable ID
    next_var: u32,
    /// Collected errors
    errors: Vec<TypeError>,
    /// In-scope type parameters (e.g., T, U in generic functions)
    type_param_scope: FxHashMap<SmolStr, Ty>,
}

impl<'a> TypeChecker<'a> {
    /// Create a new type checker.
    pub fn new(file: &'a SourceFile) -> Self {
        let mut env = TypeEnv::new();

        // Register built-in functions
        // Note: println and print are variadic - handled specially in infer_expr
        env.insert_mono(SmolStr::new("println"), Ty::Function {
            params: vec![],  // Variadic - handled specially
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("print"), Ty::Function {
            params: vec![],  // Variadic - handled specially
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("len"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Int)),
        });
        env.insert_mono(SmolStr::new("to_string"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::String)),
        });
        env.insert_mono(SmolStr::new("range"), Ty::Function {
            params: vec![Ty::Primitive(PrimitiveTy::Int), Ty::Primitive(PrimitiveTy::Int)],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Primitive(PrimitiveTy::Int)), size: None }),
        });

        // Core builtins: assert, panic
        env.insert_mono(SmolStr::new("assert"), Ty::Function {
            params: vec![Ty::Primitive(PrimitiveTy::Bool)],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("panic"), Ty::Function {
            params: vec![Ty::Primitive(PrimitiveTy::String)],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });

        // Resource intrinsics
        env.insert_mono(SmolStr::new("shadow_price"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Float)),
        });

        // Option constructors
        env.insert_mono(SmolStr::new("Some"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Named { name: SmolStr::new("Option"), args: vec![Ty::Var(TypeVar::new(0))] }),
        });
        env.insert_mono(SmolStr::new("None"), Ty::Named {
            name: SmolStr::new("Option"),
            args: vec![Ty::Var(TypeVar::new(0))],
        });

        // Result constructors
        env.insert_mono(SmolStr::new("Ok"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Named { name: SmolStr::new("Result"), args: vec![Ty::Var(TypeVar::new(0)), Ty::Var(TypeVar::new(1))] }),
        });
        env.insert_mono(SmolStr::new("Err"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Named { name: SmolStr::new("Result"), args: vec![Ty::Var(TypeVar::new(0)), Ty::Var(TypeVar::new(1))] }),
        });

        // Collection builtins: HashMap
        let hashmap_ty = Ty::Named { name: SmolStr::new("HashMap"), args: vec![] };
        env.insert_mono(SmolStr::new("hashmap_new"), Ty::Function {
            params: vec![],
            ret: Box::new(hashmap_ty.clone()),
        });
        env.insert_mono(SmolStr::new("hashmap_insert"), Ty::Function {
            params: vec![], // Variadic-like: (map, key, value)
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("hashmap_get"), Ty::Function {
            params: vec![], // (map, key)
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("hashmap_remove"), Ty::Function {
            params: vec![], // (map, key)
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("hashmap_contains"), Ty::Function {
            params: vec![], // (map, key)
            ret: Box::new(Ty::Primitive(PrimitiveTy::Bool)),
        });
        env.insert_mono(SmolStr::new("hashmap_len"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Int)),
        });
        env.insert_mono(SmolStr::new("hashmap_keys"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Primitive(PrimitiveTy::String)), size: None }),
        });
        env.insert_mono(SmolStr::new("hashmap_values"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("hashmap_entries"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });

        // Collection builtins: SortedMap
        let sortedmap_ty = Ty::Named { name: SmolStr::new("SortedMap"), args: vec![] };
        env.insert_mono(SmolStr::new("sortedmap_new"), Ty::Function {
            params: vec![],
            ret: Box::new(sortedmap_ty.clone()),
        });
        env.insert_mono(SmolStr::new("sortedmap_insert"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("sortedmap_get"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("sortedmap_remove"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("sortedmap_len"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Int)),
        });
        env.insert_mono(SmolStr::new("sortedmap_keys"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Primitive(PrimitiveTy::String)), size: None }),
        });
        env.insert_mono(SmolStr::new("sortedmap_min_key"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("sortedmap_max_key"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("sortedmap_range"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });

        // Collection builtins: Queue
        env.insert_mono(SmolStr::new("queue_new"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("queue_enqueue"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("queue_dequeue"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("queue_peek"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("queue_len"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Int)),
        });
        env.insert_mono(SmolStr::new("queue_is_empty"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Bool)),
        });

        // Collection builtins: PriorityQueue
        let pq_ty = Ty::Named { name: SmolStr::new("PriorityQueue"), args: vec![] };
        env.insert_mono(SmolStr::new("priority_queue_new"), Ty::Function {
            params: vec![],
            ret: Box::new(pq_ty),
        });
        env.insert_mono(SmolStr::new("priority_queue_push"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Unit)),
        });
        env.insert_mono(SmolStr::new("priority_queue_pop"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("priority_queue_peek"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Var(TypeVar::new(0))),
        });
        env.insert_mono(SmolStr::new("priority_queue_len"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Int)),
        });

        // Collection builtins: Set operations
        env.insert_mono(SmolStr::new("set_union"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("set_intersection"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("set_difference"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("set_symmetric_difference"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });
        env.insert_mono(SmolStr::new("set_is_subset"), Ty::Function {
            params: vec![],
            ret: Box::new(Ty::Primitive(PrimitiveTy::Bool)),
        });
        env.insert_mono(SmolStr::new("set_from_array"), Ty::Function {
            params: vec![Ty::Var(TypeVar::new(0))],
            ret: Box::new(Ty::Array { elem: Box::new(Ty::Var(TypeVar::new(0))), size: None }),
        });

        Self {
            file,
            env,
            substitution: FxHashMap::default(),
            next_var: 100,
            errors: Vec::new(),
            type_param_scope: FxHashMap::default(),
        }
    }

    /// Generate a fresh type variable.
    pub fn fresh_var(&mut self) -> Ty {
        let var = TypeVar::new(self.next_var);
        self.next_var += 1;
        Ty::Var(var)
    }

    /// Check all items in the file.
    pub fn check_all(&mut self) -> Vec<TypeError> {
        // First pass: collect function signatures
        for item in &self.file.items {
            self.collect_item_signature(item);
        }

        // Second pass: check function bodies
        for item in &self.file.items {
            self.check_item(item);
        }

        std::mem::take(&mut self.errors)
    }

    /// Collect the type signature of an item.
    fn collect_item_signature(&mut self, item: &Item) {
        match item {
            Item::Function(func) => {
                let ty = self.function_type(func);
                self.env.insert_mono(func.name.clone(), ty);
            }
            Item::AdaptiveFunction(func) => {
                let ty = self.adaptive_function_type(func);
                self.env.insert_mono(func.name.clone(), ty);
            }
            Item::Const(c) => {
                let ty = if let Some(ty_id) = c.ty {
                    self.resolve_ast_type(ty_id)
                } else {
                    self.fresh_var()
                };
                self.env.insert_mono(c.name.clone(), ty);
            }
            Item::TypeDef(td) => {
                self.collect_typedef_info(td);
            }
            Item::Import(_) => {}
            Item::TraitDecl(t) => {
                self.collect_trait_info(t);
            }
            Item::ImplBlock(i) => {
                self.collect_impl_info(i);
            }
            Item::ModuleDecl(m) => {
                // Recursively collect signatures from module items
                if let Some(items) = &m.items {
                    for item in items {
                        self.collect_item_signature(item);
                    }
                }
            }
            Item::StaticDecl(s) => {
                let ty = self.resolve_ast_type(s.ty);
                self.env.insert_mono(s.name.clone(), ty);
            }
            Item::EffectDecl(_) | Item::ExternBlock(_) => {}
            Item::Error(_) => {}
        }
    }

    /// Collect struct field information from a type definition.
    fn collect_typedef_info(&mut self, td: &eclexia_ast::TypeDef) {
        match &td.kind {
            eclexia_ast::TypeDefKind::Struct(fields) => {
                let field_info: Vec<(SmolStr, Ty)> = fields
                    .iter()
                    .map(|f| {
                        let ty = self.resolve_ast_type(f.ty);
                        (f.name.clone(), ty)
                    })
                    .collect();
                self.env.register_struct(td.name.clone(), field_info);
            }
            eclexia_ast::TypeDefKind::Enum(variants) => {
                // Register each variant as a constructor function
                for v in variants {
                    if let Some(fields) = &v.fields {
                        let param_tys: Vec<Ty> = fields.iter().map(|&f| self.resolve_ast_type(f)).collect();
                        let constructor_ty = Ty::Function {
                            params: param_tys,
                            ret: Box::new(Ty::Named { name: td.name.clone(), args: vec![] }),
                        };
                        self.env.insert_mono(v.name.clone(), constructor_ty);
                    } else {
                        // Unit variant: just a value of the enum type
                        self.env.insert_mono(v.name.clone(), Ty::Named { name: td.name.clone(), args: vec![] });
                    }
                }
            }
            eclexia_ast::TypeDefKind::Alias(target) => {
                let target_ty = self.resolve_ast_type(*target);
                self.env.insert_mono(td.name.clone(), target_ty);
            }
        }
    }

    /// Collect trait method information.
    fn collect_trait_info(&mut self, t: &eclexia_ast::TraitDecl) {
        let mut methods = Vec::new();
        for item in &t.items {
            if let eclexia_ast::TraitItem::Method { sig, .. } = item {
                let ty = self.function_sig_type(sig);
                methods.push((sig.name.clone(), ty));
            }
        }
        self.env.register_trait(t.name.clone(), methods);
    }

    /// Collect impl block method information.
    fn collect_impl_info(&mut self, i: &eclexia_ast::ImplBlock) {
        let self_ty_name = match &self.file.types[i.self_ty].kind {
            eclexia_ast::TypeKind::Named { name, .. } => name.clone(),
            _ => return,
        };

        let mut methods = Vec::new();
        for item in &i.items {
            if let eclexia_ast::ImplItem::Method { sig, .. } = item {
                let ty = self.function_sig_type(sig);
                methods.push((sig.name.clone(), ty.clone()));
                // Also register method globally as Type::method
                let qualified_name = SmolStr::new(format!("{}::{}", self_ty_name, sig.name));
                self.env.insert_mono(qualified_name, ty);
            }
        }
        self.env.register_impl_methods(self_ty_name, methods);
    }

    /// Get function type from a FunctionSig.
    fn function_sig_type(&mut self, sig: &eclexia_ast::FunctionSig) -> Ty {
        let params: Vec<Ty> = sig.params.iter().map(|p| {
            if let Some(ty_id) = p.ty {
                self.resolve_ast_type(ty_id)
            } else {
                self.fresh_var()
            }
        }).collect();

        let ret = if let Some(ty_id) = sig.return_type {
            self.resolve_ast_type(ty_id)
        } else {
            self.fresh_var()
        };

        Ty::Function {
            params,
            ret: Box::new(ret),
        }
    }

    /// Get the function type from a function definition.
    fn function_type(&mut self, func: &Function) -> Ty {
        // Register generic type parameters as fresh type variables
        self.type_param_scope.clear();
        for tp in &func.type_params {
            let var = self.fresh_var();
            self.type_param_scope.insert(tp.clone(), var);
        }

        let params: Vec<Ty> = func.params.iter().map(|p| {
            if let Some(ty_id) = p.ty {
                self.resolve_ast_type(ty_id)
            } else {
                self.fresh_var()
            }
        }).collect();

        let ret = if let Some(ty_id) = func.return_type {
            self.resolve_ast_type(ty_id)
        } else {
            // Create a fresh type variable for inferred return type
            self.fresh_var()
        };

        self.type_param_scope.clear();

        Ty::Function {
            params,
            ret: Box::new(ret),
        }
    }

    /// Get the function type from an adaptive function definition.
    fn adaptive_function_type(&mut self, func: &AdaptiveFunction) -> Ty {
        // Adaptive functions may also have type params (clear scope)
        self.type_param_scope.clear();

        let params: Vec<Ty> = func.params.iter().map(|p| {
            if let Some(ty_id) = p.ty {
                self.resolve_ast_type(ty_id)
            } else {
                self.fresh_var()
            }
        }).collect();

        let ret = if let Some(ty_id) = func.return_type {
            self.resolve_ast_type(ty_id)
        } else {
            // Create a fresh type variable for inferred return type
            self.fresh_var()
        };

        Ty::Function {
            params,
            ret: Box::new(ret),
        }
    }

    /// Resolve an AST type to a semantic type.
    fn resolve_ast_type(&mut self, ty_id: eclexia_ast::TypeId) -> Ty {
        let ty = &self.file.types[ty_id];
        self.convert_ast_type(ty)
    }

    /// Convert an AST Type to a semantic Ty.
    fn convert_ast_type(&mut self, ty: &eclexia_ast::Type) -> Ty {
        match &ty.kind {
            eclexia_ast::TypeKind::Named { name, args } => {
                if args.is_empty() {
                    // Check if this is a generic type parameter
                    if let Some(ty) = self.type_param_scope.get(name) {
                        return ty.clone();
                    }
                    match name.as_str() {
                        "Int" | "int" => Ty::Primitive(PrimitiveTy::Int),
                        "Float" | "float" => Ty::Primitive(PrimitiveTy::Float),
                        "Bool" | "bool" => Ty::Primitive(PrimitiveTy::Bool),
                        "String" | "string" => Ty::Primitive(PrimitiveTy::String),
                        "Char" | "char" => Ty::Primitive(PrimitiveTy::Char),
                        "Unit" | "unit" => Ty::Primitive(PrimitiveTy::Unit),
                        "I8" | "i8" => Ty::Primitive(PrimitiveTy::I8),
                        "I16" | "i16" => Ty::Primitive(PrimitiveTy::I16),
                        "I32" | "i32" => Ty::Primitive(PrimitiveTy::I32),
                        "I64" | "i64" => Ty::Primitive(PrimitiveTy::I64),
                        "U8" | "u8" => Ty::Primitive(PrimitiveTy::U8),
                        "U16" | "u16" => Ty::Primitive(PrimitiveTy::U16),
                        "U32" | "u32" => Ty::Primitive(PrimitiveTy::U32),
                        "U64" | "u64" => Ty::Primitive(PrimitiveTy::U64),
                        "F32" | "f32" => Ty::Primitive(PrimitiveTy::F32),
                        "F64" | "f64" => Ty::Primitive(PrimitiveTy::F64),
                        _ => Ty::Named { name: name.clone(), args: vec![] },
                    }
                } else {
                    let arg_tys: Vec<Ty> = args.iter().map(|a| self.resolve_ast_type(*a)).collect();
                    Ty::Named { name: name.clone(), args: arg_tys }
                }
            }
            eclexia_ast::TypeKind::Array { elem, size } => {
                let elem_ty = self.resolve_ast_type(*elem);
                Ty::Array { elem: Box::new(elem_ty), size: *size }
            }
            eclexia_ast::TypeKind::Tuple(elems) => {
                let elem_tys: Vec<Ty> = elems.iter().map(|e| self.resolve_ast_type(*e)).collect();
                Ty::Tuple(elem_tys)
            }
            eclexia_ast::TypeKind::Function { params, ret } => {
                let param_tys: Vec<Ty> = params.iter().map(|p| self.resolve_ast_type(*p)).collect();
                let ret_ty = self.resolve_ast_type(*ret);
                Ty::Function { params: param_tys, ret: Box::new(ret_ty) }
            }
            eclexia_ast::TypeKind::Resource { base, dimension } => {
                let base_ty = match base.as_str() {
                    "Float" | "F64" => PrimitiveTy::Float,
                    "Int" | "I64" => PrimitiveTy::Int,
                    _ => PrimitiveTy::Float,
                };
                Ty::Resource { base: base_ty, dimension: dimension.clone() }
            }
            eclexia_ast::TypeKind::Reference { ty, mutable } => {
                let inner_ty = self.resolve_ast_type(*ty);
                Ty::Named {
                    name: if *mutable { SmolStr::new("&mut") } else { SmolStr::new("&") },
                    args: vec![inner_ty],
                }
            }
            eclexia_ast::TypeKind::Optional(inner) => {
                let inner_ty = self.resolve_ast_type(*inner);
                Ty::Named {
                    name: SmolStr::new("Option"),
                    args: vec![inner_ty],
                }
            }
            eclexia_ast::TypeKind::Infer => self.fresh_var(),
            eclexia_ast::TypeKind::Error => Ty::Error,
        }
    }

    /// Check an item.
    fn check_item(&mut self, item: &Item) {
        match item {
            Item::Function(func) => self.check_function(func),
            Item::AdaptiveFunction(func) => self.check_adaptive_function(func),
            Item::Const(c) => {
                let expr_ty = self.infer_expr(c.value);
                let expected_ty = self.env.lookup(&c.name).map(|s| s.ty.clone());
                if let Some(expected) = expected_ty {
                    if let Err(e) = self.unify(&expected, &expr_ty, self.file.exprs[c.value].span) {
                        self.errors.push(e);
                    }
                }
            }
            Item::TypeDef(_) | Item::Import(_) => {}
            Item::ImplBlock(i) => {
                // Type-check impl block method bodies
                for impl_item in &i.items {
                    if let eclexia_ast::ImplItem::Method { sig, body, .. } = impl_item {
                        let mut body_env = self.env.child();
                        for param in &sig.params {
                            let ty = if let Some(ty_id) = param.ty {
                                self.resolve_ast_type(ty_id)
                            } else {
                                self.fresh_var()
                            };
                            body_env.insert_mono(param.name.clone(), ty);
                        }
                        let old_env = std::mem::replace(&mut self.env, body_env);
                        self.check_block(body);
                        self.env = old_env;
                    }
                }
            }
            Item::ModuleDecl(m) => {
                if let Some(items) = &m.items {
                    for item in items {
                        self.check_item(item);
                    }
                }
            }
            Item::StaticDecl(s) => {
                let value_ty = self.infer_expr(s.value);
                let declared_ty = self.resolve_ast_type(s.ty);
                if let Err(e) = self.unify(&declared_ty, &value_ty, s.span) {
                    self.errors.push(e);
                }
            }
            Item::TraitDecl(_)
            | Item::EffectDecl(_)
            | Item::ExternBlock(_) => {}
            Item::Error(_) => {}
        }
    }

    /// Check a function body.
    fn check_function(&mut self, func: &Function) {
        // Extract function type info before borrowing self mutably
        let func_info = self.env.lookup(&func.name).and_then(|scheme| {
            if let Ty::Function { params, ret } = &scheme.ty {
                Some((params.clone(), (**ret).clone()))
            } else {
                None
            }
        });

        if let Some((params, ret_ty)) = func_info {
            let mut body_env = self.env.child();
            for (param, param_ty) in func.params.iter().zip(params.iter()) {
                body_env.insert_mono(param.name.clone(), param_ty.clone());
            }

            let old_env = std::mem::replace(&mut self.env, body_env);
            let body_ty = self.check_block(&func.body);
            self.env = old_env;

            if let Err(e) = self.unify(&ret_ty, &body_ty, func.span) {
                self.errors.push(e);
            }

            // Check resource constraints
            self.check_constraints(&func.constraints);
        }
    }

    /// Check an adaptive function.
    fn check_adaptive_function(&mut self, func: &AdaptiveFunction) {
        // Extract function type info before borrowing self mutably
        let func_info = self.env.lookup(&func.name).and_then(|scheme| {
            if let Ty::Function { params, ret } = &scheme.ty {
                Some((params.clone(), (**ret).clone()))
            } else {
                None
            }
        });

        let Some((params, ret_ty)) = func_info else {
            return;
        };

        // Check function-level constraints
        self.check_constraints(&func.constraints);

        for solution in &func.solutions {
            let mut body_env = self.env.child();
            for (param, param_ty) in func.params.iter().zip(params.iter()) {
                body_env.insert_mono(param.name.clone(), param_ty.clone());
            }

            let old_env = std::mem::replace(&mut self.env, body_env);
            let body_ty = self.check_block(&solution.body);
            self.env = old_env;

            if let Err(e) = self.unify(&ret_ty, &body_ty, solution.span) {
                self.errors.push(e);
            }

            // Check solution-level resource provisions
            self.check_resource_provisions(&solution.provides);
        }
    }

    /// Check a block and return its type.
    fn check_block(&mut self, block: &Block) -> Ty {
        for stmt_id in &block.stmts {
            self.check_stmt(*stmt_id);
        }

        if let Some(expr) = block.expr {
            self.infer_expr(expr)
        } else {
            Ty::Primitive(PrimitiveTy::Unit)
        }
    }

    /// Check a statement.
    fn check_stmt(&mut self, stmt_id: StmtId) {
        let stmt = &self.file.stmts[stmt_id];

        match &stmt.kind {
            StmtKind::Let { pattern, mutable: _, ty, value } => {
                let inferred = self.infer_expr(*value);
                let binding_ty = if let Some(ty_id) = ty {
                    let declared = self.resolve_ast_type(*ty_id);
                    if let Err(e) = self.unify(&declared, &inferred, stmt.span) {
                        self.errors.push(e);
                    }
                    declared
                } else {
                    inferred
                };

                // Recursively bind pattern variables
                self.bind_pattern(pattern, &binding_ty, stmt.span);
            }
            StmtKind::Expr(expr) => {
                self.infer_expr(*expr);
            }
            StmtKind::Return(expr) => {
                if let Some(e) = expr {
                    self.infer_expr(*e);
                }
            }
            StmtKind::While { condition, body } => {
                let cond_ty = self.infer_expr(*condition);
                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), &cond_ty, self.file.exprs[*condition].span) {
                    self.errors.push(e);
                }
                self.check_block(body);
            }
            StmtKind::For { pattern, iter, body } => {
                let iter_ty = self.infer_expr(*iter);

                let elem_ty = match &iter_ty {
                    Ty::Array { elem, .. } => (**elem).clone(),
                    _ => {
                        self.errors.push(TypeError::Custom {
                            span: self.file.exprs[*iter].span,
                            message: format!("expected iterable, found {}", iter_ty),
                            hint: None,
                        });
                        Ty::Error
                    }
                };

                let loop_env = self.env.child();
                let old_env = std::mem::replace(&mut self.env, loop_env);
                // Bind pattern variables in loop scope
                self.bind_pattern(pattern, &elem_ty, stmt.span);
                self.check_block(body);
                self.env = old_env;
            }
            StmtKind::Assign { target, value } => {
                // Type check the value
                let value_ty = self.infer_expr(*value);

                // Look up the target expression to get the variable name
                let target_expr = &self.file.exprs[*target];
                match &target_expr.kind {
                    ExprKind::Var(name) => {
                        // Check that target variable exists and types match
                        if let Some(target_scheme) = self.env.lookup(name.as_str()) {
                            let target_ty = target_scheme.ty.clone();
                            if let Err(e) = self.unify(&target_ty, &value_ty, stmt.span) {
                                self.errors.push(e);
                            }
                        } else {
                            self.errors.push(TypeError::Custom {
                                span: stmt.span,
                                message: format!("undefined variable: {}", name),
                                hint: Some("variables must be declared with 'let' before assignment".to_string()),
                            });
                        }
                    }
                    _ => {
                        // For field/index assignment, just type-check both sides
                        let _target_ty = self.infer_expr(*target);
                    }
                }
            }
            StmtKind::Loop { label: _, body } => {
                self.check_block(body);
            }
            StmtKind::Break { label: _, value } => {
                if let Some(e) = value {
                    self.infer_expr(*e);
                }
            }
            StmtKind::Continue { label: _ } => {
                // Nothing to type-check
            }
            StmtKind::Error => {}
        }
    }

    /// Infer the type of an expression.
    fn infer_expr(&mut self, expr_id: ExprId) -> Ty {
        let expr = &self.file.exprs[expr_id];

        match &expr.kind {
            ExprKind::Literal(lit) => self.literal_type(lit),

            ExprKind::Var(name) => {
                if let Some(scheme) = self.env.lookup(name.as_str()) {
                    scheme.ty.clone()
                } else {
                    // Collect available variable names for suggestions
                    let available = self.env.available_names();
                    let available_refs: Vec<&str> = available.iter().map(|s| s.as_str()).collect();
                    self.errors.push(TypeError::undefined_with_suggestions(
                        expr.span,
                        name.to_string(),
                        &available_refs,
                    ));
                    Ty::Error
                }
            }

            ExprKind::Binary { op, lhs, rhs } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);
                self.binary_op_type(*op, &lhs_ty, &rhs_ty, expr.span)
            }

            ExprKind::Unary { op, operand } => {
                let op_ty = self.infer_expr(*operand);
                self.unary_op_type(*op, &op_ty, expr.span)
            }

            ExprKind::Call { func, args } => {
                let func_ty = self.infer_expr(*func);
                let arg_tys: Vec<Ty> = args.iter().map(|a| self.infer_expr(*a)).collect();

                match func_ty {
                    Ty::Function { params, ret } => {
                        // Empty params means variadic function (e.g., println, print)
                        if !params.is_empty() {
                            if params.len() != arg_tys.len() {
                                self.errors.push(TypeError::Custom {
                                    span: expr.span,
                                    message: format!("expected {} arguments, found {}", params.len(), arg_tys.len()),
                            hint: None,
                                });
                            } else {
                                for (param, arg) in params.iter().zip(arg_tys.iter()) {
                                    if !matches!(param, Ty::Var(_)) {
                                        if let Err(e) = self.unify(param, arg, expr.span) {
                                            self.errors.push(e);
                                        }
                                    }
                                }
                            }
                        }
                        // For variadic functions, still infer arg types but don't check counts
                        *ret
                    }
                    Ty::Error => Ty::Error,
                    _ => {
                        self.errors.push(TypeError::Custom {
                            span: expr.span,
                            message: format!("expected function, found {}", func_ty),
                            hint: None,
                        });
                        Ty::Error
                    }
                }
            }

            ExprKind::If { condition, then_branch, else_branch } => {
                let cond_ty = self.infer_expr(*condition);
                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), &cond_ty, self.file.exprs[*condition].span) {
                    self.errors.push(e);
                }

                let then_ty = self.check_block(then_branch);

                if let Some(else_block) = else_branch {
                    let else_ty = self.check_block(else_block);
                    if let Err(e) = self.unify(&then_ty, &else_ty, expr.span) {
                        self.errors.push(e);
                    }
                    then_ty
                } else {
                    Ty::Primitive(PrimitiveTy::Unit)
                }
            }

            ExprKind::Block(block) => self.check_block(block),

            ExprKind::Tuple(elems) => {
                let elem_tys: Vec<Ty> = elems.iter().map(|e| self.infer_expr(*e)).collect();
                Ty::Tuple(elem_tys)
            }

            ExprKind::Array(elems) => {
                if elems.is_empty() {
                    Ty::Array { elem: Box::new(self.fresh_var()), size: Some(0) }
                } else {
                    let first_ty = self.infer_expr(elems[0]);
                    for elem in elems.iter().skip(1) {
                        let elem_ty = self.infer_expr(*elem);
                        if let Err(e) = self.unify(&first_ty, &elem_ty, self.file.exprs[*elem].span) {
                            self.errors.push(e);
                        }
                    }
                    Ty::Array { elem: Box::new(first_ty), size: Some(elems.len()) }
                }
            }

            ExprKind::Index { expr: arr, index } => {
                let arr_ty = self.infer_expr(*arr);
                let idx_ty = self.infer_expr(*index);

                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Int), &idx_ty, self.file.exprs[*index].span) {
                    self.errors.push(e);
                }

                match arr_ty {
                    Ty::Array { elem, .. } => *elem,
                    Ty::Tuple(elems) => {
                        if elems.is_empty() {
                            Ty::Error
                        } else {
                            elems[0].clone()
                        }
                    }
                    _ => {
                        self.errors.push(TypeError::Custom {
                            span: expr.span,
                            message: format!("expected array or tuple, found {}", arr_ty),
                            hint: None,
                        });
                        Ty::Error
                    }
                }
            }

            ExprKind::Field { expr: obj, field } => {
                let obj_ty = self.infer_expr(*obj);
                match &obj_ty {
                    Ty::Named { name, .. } => {
                        // Look up field type from struct definition
                        if let Some(field_ty) = self.env.lookup_field(name.as_str(), field.as_str()) {
                            field_ty
                        } else {
                            self.fresh_var()
                        }
                    }
                    Ty::Tuple(elems) => {
                        // Numeric field access on tuples (e.g., tuple.0)
                        if let Ok(idx) = field.as_str().parse::<usize>() {
                            if idx < elems.len() {
                                elems[idx].clone()
                            } else {
                                self.errors.push(TypeError::Custom {
                                    span: expr.span,
                                    message: format!("tuple index {} out of bounds (tuple has {} elements)", idx, elems.len()),
                                    hint: None,
                                });
                                Ty::Error
                            }
                        } else {
                            self.errors.push(TypeError::Custom {
                                span: expr.span,
                                message: format!("cannot access field '{}' on tuple type", field),
                                hint: Some("use numeric indices for tuples (e.g., .0, .1)".to_string()),
                            });
                            Ty::Error
                        }
                    }
                    _ => {
                        self.errors.push(TypeError::Custom {
                            span: expr.span,
                            message: format!("cannot access field '{}' on type {}", field, obj_ty),
                            hint: None,
                        });
                        Ty::Error
                    }
                }
            }

            ExprKind::Lambda { params, body: _ } => {
                let param_tys: Vec<Ty> = params.iter().map(|p| {
                    if let Some(ty_id) = p.ty {
                        self.resolve_ast_type(ty_id)
                    } else {
                        self.fresh_var()
                    }
                }).collect();
                let ret_ty = self.fresh_var();
                Ty::Function { params: param_tys, ret: Box::new(ret_ty) }
            }

            ExprKind::Match { scrutinee, arms } => {
                let scrut_ty = self.infer_expr(*scrutinee);

                if arms.is_empty() {
                    return Ty::Primitive(PrimitiveTy::Unit);
                }

                // Type check each arm
                let mut result_ty: Option<Ty> = None;
                for arm in arms {
                    // Check pattern against scrutinee type
                    self.check_pattern_type(&arm.pattern, &scrut_ty, expr.span);

                    // Check guard if present
                    if let Some(guard) = arm.guard {
                        let guard_ty = self.infer_expr(guard);
                        if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), &guard_ty, expr.span) {
                            self.errors.push(e);
                        }
                    }

                    // Bind pattern variables and check body
                    let arm_env = self.env.child();
                    let old_env = std::mem::replace(&mut self.env, arm_env);
                    self.bind_pattern(&arm.pattern, &scrut_ty, arm.span);
                    let arm_ty = self.infer_expr(arm.body);
                    self.env = old_env;

                    // Unify all arm types
                    if let Some(ref prev_ty) = result_ty {
                        if let Err(e) = self.unify(prev_ty, &arm_ty, arm.span) {
                            self.errors.push(e);
                        }
                    } else {
                        result_ty = Some(arm_ty);
                    }
                }

                result_ty.unwrap_or(Ty::Primitive(PrimitiveTy::Unit))
            }

            ExprKind::MethodCall { receiver, method, args } => {
                let recv_ty = self.infer_expr(*receiver);
                let arg_tys: Vec<Ty> = args.iter().map(|a| self.infer_expr(*a)).collect();

                // 1. Check impl methods for the receiver type
                let type_name = match &recv_ty {
                    Ty::Named { name, .. } => Some(name.clone()),
                    _ => None,
                };
                if let Some(ref tn) = type_name {
                    if let Some(method_ty) = self.env.lookup_method(tn.as_str(), method.as_str()) {
                        if let Ty::Function { params, ret } = &method_ty {
                            // Check arg count (minus self param)
                            let expected = if params.is_empty() { 0 } else { params.len().saturating_sub(1) };
                            if !params.is_empty() && arg_tys.len() != expected {
                                self.errors.push(TypeError::Custom {
                                    span: expr.span,
                                    message: format!("expected {} arguments, found {}", expected, arg_tys.len()),
                                    hint: None,
                                });
                            }
                            return (**ret).clone();
                        }
                        return method_ty;
                    }
                }

                // 2. Check globally registered function
                if let Some(scheme) = self.env.lookup(method.as_str()) {
                    if let Ty::Function { ret, .. } = &scheme.ty {
                        return (**ret).clone();
                    }
                }

                // 3. Built-in methods
                match (method.as_str(), &recv_ty) {
                    ("to_string", _) => Ty::Primitive(PrimitiveTy::String),
                    ("len", Ty::Array { .. }) | ("len", Ty::Primitive(PrimitiveTy::String)) => {
                        Ty::Primitive(PrimitiveTy::Int)
                    }
                    ("push", Ty::Array { elem, .. }) => {
                        if let Some(arg) = arg_tys.first() {
                            if let Err(e) = self.unify(elem, arg, expr.span) {
                                self.errors.push(e);
                            }
                        }
                        Ty::Primitive(PrimitiveTy::Unit)
                    }
                    ("pop", Ty::Array { elem, .. }) => (**elem).clone(),
                    ("contains", Ty::Array { .. }) => Ty::Primitive(PrimitiveTy::Bool),
                    ("is_empty", Ty::Array { .. }) => Ty::Primitive(PrimitiveTy::Bool),
                    ("clone", _) => recv_ty.clone(),
                    _ => self.fresh_var()
                }
            }

            ExprKind::Struct { name, fields } => {
                for (_, field_expr) in fields {
                    self.infer_expr(*field_expr);
                }
                Ty::Named { name: name.clone(), args: vec![] }
            }

            ExprKind::Resource(_) => {
                Ty::Primitive(PrimitiveTy::Float)
            }

            ExprKind::Cast { expr: inner, target_ty } => {
                let source_ty = self.infer_expr(*inner);
                let target = self.resolve_ast_type(*target_ty);

                // Validate cast: numeric-to-numeric, or same type
                let valid = match (&source_ty, &target) {
                    (Ty::Primitive(s), Ty::Primitive(t)) => {
                        s.is_numeric() && t.is_numeric()
                            || s == t
                            || (s.is_integer() && *t == PrimitiveTy::Char)
                            || (*s == PrimitiveTy::Char && t.is_integer())
                    }
                    (Ty::Error, _) | (_, Ty::Error) => true,
                    (Ty::Var(_), _) | (_, Ty::Var(_)) => true, // Allow casts involving type vars
                    _ => false,
                };

                if !valid {
                    self.errors.push(TypeError::Custom {
                        span: expr.span,
                        message: format!("cannot cast {} to {}", source_ty, target),
                        hint: Some("casts are only valid between numeric types".to_string()),
                    });
                }
                target
            }

            ExprKind::ArrayRepeat { value, count } => {
                let elem_ty = self.infer_expr(*value);
                let count_ty = self.infer_expr(*count);
                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Int), &count_ty, expr.span) {
                    self.errors.push(e);
                }
                Ty::Array { elem: Box::new(elem_ty), size: None }
            }
            ExprKind::Try(inner) => {
                let inner_ty = self.infer_expr(*inner);
                // Try operator unwraps Optional<T> → T or Result<T,E> → T
                match &inner_ty {
                    Ty::Named { name, args } if name.as_str() == "Option" || name.as_str() == "Result" => {
                        args.first().cloned().unwrap_or(Ty::Primitive(PrimitiveTy::Unit))
                    }
                    _ => inner_ty, // Pass through for now
                }
            }
            ExprKind::Borrow { expr: inner, mutable } => {
                let inner_ty = self.infer_expr(*inner);
                Ty::Named {
                    name: if *mutable { SmolStr::new("&mut") } else { SmolStr::new("&") },
                    args: vec![inner_ty],
                }
            }
            ExprKind::Deref(inner) => {
                let inner_ty = self.infer_expr(*inner);
                // Dereference &T → T
                match &inner_ty {
                    Ty::Named { name, args } if (name.as_str() == "&" || name.as_str() == "&mut") && !args.is_empty() => {
                        args[0].clone()
                    }
                    _ => inner_ty,
                }
            }
            ExprKind::AsyncBlock(block) => {
                // Not yet implemented: should return Future<T>
                self.check_block(block)
            }
            ExprKind::Await(inner) => {
                // Not yet implemented: should unwrap Future<T> to T
                self.infer_expr(*inner)
            }
            ExprKind::Handle { expr: inner, handlers: _ } => {
                // Not yet implemented: effect handling
                self.infer_expr(*inner)
            }
            ExprKind::ReturnExpr(value) => {
                if let Some(e) = value {
                    self.infer_expr(*e);
                }
                // Return expressions diverge
                Ty::Primitive(PrimitiveTy::Unit)
            }
            ExprKind::BreakExpr { label: _, value } => {
                if let Some(e) = value {
                    self.infer_expr(*e);
                }
                Ty::Primitive(PrimitiveTy::Unit)
            }
            ExprKind::ContinueExpr { label: _ } => {
                Ty::Primitive(PrimitiveTy::Unit)
            }
            ExprKind::PathExpr(segments) => {
                // Not yet implemented: path resolution
                // Try looking up the last segment as a variable
                if let Some(last) = segments.last() {
                    if let Some(scheme) = self.env.lookup(last.as_str()) {
                        return scheme.ty.clone();
                    }
                }
                Ty::Error
            }

            ExprKind::Error => Ty::Error,
        }
    }

    /// Recursively bind pattern variables to types in the environment.
    fn bind_pattern(&mut self, pattern: &Pattern, ty: &Ty, span: eclexia_ast::span::Span) {
        match pattern {
            Pattern::Var(name) => {
                self.env.insert_mono(name.clone(), ty.clone());
            }
            Pattern::Wildcard | Pattern::Rest => {}
            Pattern::Tuple(pats) => {
                if let Ty::Tuple(elem_tys) = ty {
                    for (pat, elem_ty) in pats.iter().zip(elem_tys.iter()) {
                        self.bind_pattern(pat, elem_ty, span);
                    }
                } else {
                    // If not a tuple type, bind each sub-pattern to a fresh var
                    for pat in pats {
                        let fresh = self.fresh_var();
                        self.bind_pattern(pat, &fresh, span);
                    }
                }
            }
            Pattern::Constructor { fields, .. } => {
                for pat in fields {
                    let fresh = self.fresh_var();
                    self.bind_pattern(pat, &fresh, span);
                }
            }
            Pattern::Struct { fields, .. } => {
                for fp in fields {
                    if let Some(ref inner_pat) = fp.pattern {
                        let fresh = self.fresh_var();
                        self.bind_pattern(inner_pat, &fresh, span);
                    } else {
                        // Shorthand: `Point { x, y }` → bind x, y
                        let fresh = self.fresh_var();
                        self.env.insert_mono(fp.name.clone(), fresh);
                    }
                }
            }
            Pattern::Binding { name, pattern: inner } => {
                self.env.insert_mono(name.clone(), ty.clone());
                self.bind_pattern(inner, ty, span);
            }
            Pattern::Reference { pattern: inner, .. } => {
                // &pat → bind inner with the referenced type
                let inner_ty = match ty {
                    Ty::Named { name, args } if (name.as_str() == "&" || name.as_str() == "&mut") && !args.is_empty() => {
                        args[0].clone()
                    }
                    _ => ty.clone(),
                };
                self.bind_pattern(inner, &inner_ty, span);
            }
            Pattern::Or(alternatives) => {
                // For or-patterns, bind from the first alternative
                if let Some(first) = alternatives.first() {
                    self.bind_pattern(first, ty, span);
                }
            }
            Pattern::Slice(pats) => {
                let elem_ty = match ty {
                    Ty::Array { elem, .. } => (**elem).clone(),
                    _ => {
                        let fresh = self.fresh_var();
                        fresh
                    }
                };
                for pat in pats {
                    self.bind_pattern(pat, &elem_ty, span);
                }
            }
            Pattern::Literal(_) | Pattern::Range { .. } => {}
        }
    }

    /// Check that a pattern is consistent with a scrutinee type.
    fn check_pattern_type(&mut self, pattern: &Pattern, scrut_ty: &Ty, span: eclexia_ast::span::Span) {
        match pattern {
            Pattern::Literal(lit) => {
                let lit_ty = self.literal_type(lit);
                if let Err(e) = self.unify(scrut_ty, &lit_ty, span) {
                    self.errors.push(e);
                }
            }
            Pattern::Constructor { name, .. } => {
                // Check that constructor belongs to the scrutinee type
                if let Some(scheme) = self.env.lookup(name.as_str()) {
                    let constructor_ty = scheme.ty.clone();
                    if let Ty::Function { ret, .. } = &constructor_ty {
                        if let Err(e) = self.unify(scrut_ty, ret, span) {
                            self.errors.push(e);
                        }
                    }
                }
            }
            Pattern::Tuple(pats) => {
                if let Ty::Tuple(elem_tys) = scrut_ty {
                    if pats.len() != elem_tys.len() {
                        self.errors.push(TypeError::Custom {
                            span,
                            message: format!("expected tuple of {} elements, found pattern with {}", elem_tys.len(), pats.len()),
                            hint: None,
                        });
                    }
                    for (pat, ty) in pats.iter().zip(elem_tys.iter()) {
                        self.check_pattern_type(pat, ty, span);
                    }
                }
            }
            Pattern::Or(alts) => {
                for alt in alts {
                    self.check_pattern_type(alt, scrut_ty, span);
                }
            }
            _ => {} // Var, Wildcard, Rest, Binding, Reference, Struct, Slice, Range - checked elsewhere
        }
    }

    /// Get the type of a literal.
    fn literal_type(&self, lit: &Literal) -> Ty {
        match lit {
            Literal::Int(_) => Ty::Primitive(PrimitiveTy::Int),
            Literal::Float(_) => Ty::Primitive(PrimitiveTy::Float),
            Literal::String(_) => Ty::Primitive(PrimitiveTy::String),
            Literal::Char(_) => Ty::Primitive(PrimitiveTy::Char),
            Literal::Bool(_) => Ty::Primitive(PrimitiveTy::Bool),
            Literal::Unit => Ty::Primitive(PrimitiveTy::Unit),
        }
    }

    /// Get the result type of a binary operation.
    fn binary_op_type(&mut self, op: BinaryOp, lhs: &Ty, rhs: &Ty, span: eclexia_ast::span::Span) -> Ty {
        match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem | BinaryOp::Pow => {
                // Handle dimensional type checking for Resource types
                match (lhs, rhs, op) {
                    // Resource + Resource (must have same dimension)
                    (Ty::Resource { base: b1, dimension: d1 }, Ty::Resource { base: b2, dimension: d2 }, BinaryOp::Add | BinaryOp::Sub) => {
                        if d1 != d2 {
                            self.errors.push(TypeError::DimensionMismatch {
                                span,
                                dim1: d1.to_string(),
                                dim2: d2.to_string(),
                                hint: Some("resources can only be added/subtracted if they have the same dimension".to_string()),
                            });
                            return Ty::Error;
                        }
                        // Base types should be compatible
                        if b1 != b2 {
                            self.errors.push(TypeError::Custom {
                                span,
                                message: format!("cannot add {} and {} (incompatible base types)", b1.name(), b2.name()),
                            hint: None,
                            });
                            return Ty::Error;
                        }
                        Ty::Resource { base: *b1, dimension: *d1 }
                    }

                    // Resource * Resource (dimensions multiply)
                    (Ty::Resource { base: b1, dimension: d1 }, Ty::Resource { base: b2, dimension: d2 }, BinaryOp::Mul) => {
                        let result_dim = d1.multiply(d2);
                        // Upgrade base type if necessary (Int * Float = Float)
                        let result_base = if b1.is_float() || b2.is_float() {
                            PrimitiveTy::Float
                        } else {
                            *b1
                        };
                        Ty::Resource { base: result_base, dimension: result_dim }
                    }

                    // Resource / Resource (dimensions divide)
                    (Ty::Resource { base: _b1, dimension: d1 }, Ty::Resource { base: _b2, dimension: d2 }, BinaryOp::Div) => {
                        let result_dim = d1.divide(d2);
                        Ty::Resource { base: PrimitiveTy::Float, dimension: result_dim }
                    }

                    // Resource * Scalar (scalar multiplication)
                    (Ty::Resource { base, dimension }, Ty::Primitive(p), BinaryOp::Mul) |
                    (Ty::Primitive(p), Ty::Resource { base, dimension }, BinaryOp::Mul) if p.is_numeric() => {
                        Ty::Resource { base: *base, dimension: *dimension }
                    }

                    // Resource / Scalar (scalar division)
                    (Ty::Resource { base, dimension }, Ty::Primitive(p), BinaryOp::Div) if p.is_numeric() => {
                        Ty::Resource { base: *base, dimension: *dimension }
                    }

                    // Resource ^ Int (dimension exponentiation)
                    (Ty::Resource { base, dimension }, Ty::Primitive(p), BinaryOp::Pow) if p.is_integer() => {
                        // For now, we can't compute the exponent at compile-time
                        // In a more advanced implementation, we'd need constant evaluation
                        self.errors.push(TypeError::Custom {
                            span,
                            message: "resource exponentiation requires constant integer exponent (not yet implemented)".to_string(),
                            hint: None,
                        });
                        Ty::Error
                    }

                    // Fall through to standard numeric handling
                    _ => {
                        if let Err(e) = self.unify(lhs, rhs, span) {
                            self.errors.push(e);
                        }
                        if self.is_numeric(lhs) {
                            lhs.clone()
                        } else if matches!(lhs, Ty::Primitive(PrimitiveTy::String)) && op == BinaryOp::Add {
                            Ty::Primitive(PrimitiveTy::String)
                        } else {
                            self.errors.push(TypeError::Custom {
                                span,
                                message: format!("cannot apply {:?} to {} and {}", op, lhs, rhs),
                            hint: None,
                            });
                            Ty::Error
                        }
                    }
                }
            }
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                Ty::Primitive(PrimitiveTy::Bool)
            }
            BinaryOp::And | BinaryOp::Or => {
                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), lhs, span) {
                    self.errors.push(e);
                }
                if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), rhs, span) {
                    self.errors.push(e);
                }
                Ty::Primitive(PrimitiveTy::Bool)
            }
            BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor | BinaryOp::Shl | BinaryOp::Shr => {
                if let Err(e) = self.unify(lhs, rhs, span) {
                    self.errors.push(e);
                }
                if self.is_integer(lhs) {
                    lhs.clone()
                } else {
                    self.errors.push(TypeError::Custom {
                        span,
                        message: format!("bitwise operations require integers, found {}", lhs),
                            hint: None,
                    });
                    Ty::Error
                }
            }
            BinaryOp::Range | BinaryOp::RangeInclusive => {
                // Range operators: 0..5 or 0..=5
                // For now, we require both sides to be integers and return an iterable
                if !self.is_integer(lhs) || !self.is_integer(rhs) {
                    self.errors.push(TypeError::Custom {
                        span,
                        message: "range operators require integer bounds".to_string(),
                        hint: Some("ranges like 0..5 only work with integers".to_string()),
                    });
                    return Ty::Error;
                }
                // Return Array<Int> so ranges work in for loops
                Ty::Array { elem: Box::new(lhs.clone()), size: None }
            }
        }
    }

    /// Get the result type of a unary operation.
    fn unary_op_type(&mut self, op: UnaryOp, operand: &Ty, span: eclexia_ast::span::Span) -> Ty {
        match op {
            UnaryOp::Neg => {
                if self.is_numeric(operand) {
                    operand.clone()
                } else {
                    self.errors.push(TypeError::Custom {
                        span,
                        message: format!("cannot negate {}", operand),
                            hint: None,
                    });
                    Ty::Error
                }
            }
            UnaryOp::Not => Ty::Primitive(PrimitiveTy::Bool),
            UnaryOp::BitNot => {
                if self.is_integer(operand) {
                    operand.clone()
                } else {
                    self.errors.push(TypeError::Custom {
                        span,
                        message: format!("bitwise not requires integer, found {}", operand),
                            hint: None,
                    });
                    Ty::Error
                }
            }
        }
    }

    /// Check if a type is numeric.
    fn is_numeric(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Primitive(p) if p.is_numeric())
    }

    /// Check if a type is an integer.
    fn is_integer(&self, ty: &Ty) -> bool {
        matches!(ty, Ty::Primitive(p) if p.is_integer())
    }

    /// Check resource constraints on a function.
    fn check_constraints(&mut self, constraints: &[Constraint]) {
        for constraint in constraints {
            match &constraint.kind {
                ConstraintKind::Resource { resource, op: _, amount } => {
                    // Validate that the resource name is known
                    let dimension = match resource.as_str() {
                        "energy" => Dimension::energy(),
                        "time" | "latency" => Dimension::time(),
                        "memory" => Dimension::memory(),
                        "carbon" => Dimension::carbon(),
                        "power" => Dimension::power(),
                        other => {
                            self.errors.push(TypeError::ResourceViolation {
                                span: constraint.span,
                                message: format!("unknown resource type '{}'", other),
                                hint: Some("valid resource types are: energy, time, latency, memory, carbon, power".to_string()),
                            });
                            continue;
                        }
                    };

                    // Validate that the amount has correct units
                    if let Some(unit_name) = &amount.unit {
                        if let Some(unit) = eclexia_ast::dimension::parse_unit(unit_name.as_str()) {
                            if unit.dimension != dimension {
                                self.errors.push(TypeError::DimensionMismatch {
                                    span: constraint.span,
                                    dim1: dimension.to_string(),
                                    dim2: unit.dimension.to_string(),
                                    hint: Some(format!("expected {} dimension, found {}", dimension, unit.dimension)),
                                });
                            }
                        } else {
                            self.errors.push(TypeError::ResourceViolation {
                                span: constraint.span,
                                message: format!("unknown unit '{}'", unit_name),
                                hint: Some("check the spelling of the unit".to_string()),
                            });
                        }
                    }
                }
                ConstraintKind::Predicate(expr_id) => {
                    // Type check the predicate expression
                    let pred_ty = self.infer_expr(*expr_id);
                    if let Err(e) = self.unify(&Ty::Primitive(PrimitiveTy::Bool), &pred_ty, constraint.span) {
                        self.errors.push(e);
                    }
                }
            }
        }
    }

    /// Check resource provisions on a solution.
    fn check_resource_provisions(&mut self, provisions: &[eclexia_ast::ResourceProvision]) {
        for provision in provisions {
            // Validate that the resource name is known
            let dimension = match provision.resource.as_str() {
                "energy" => Dimension::energy(),
                "time" | "latency" => Dimension::time(),
                "memory" => Dimension::memory(),
                "carbon" => Dimension::carbon(),
                "power" => Dimension::power(),
                other => {
                    self.errors.push(TypeError::ResourceViolation {
                        span: provision.span,
                        message: format!("unknown resource type '{}'", other),
                        hint: Some("valid resource types are: energy, time, latency, memory, carbon, power".to_string()),
                    });
                    continue;
                }
            };

            // Validate that the amount has correct units
            if let Some(unit_name) = &provision.amount.unit {
                if let Some(unit) = eclexia_ast::dimension::parse_unit(unit_name.as_str()) {
                    if unit.dimension != dimension {
                        self.errors.push(TypeError::DimensionMismatch {
                            span: provision.span,
                            dim1: dimension.to_string(),
                            dim2: unit.dimension.to_string(),
                            hint: Some(format!("expected {} dimension, found {}", dimension, unit.dimension)),
                        });
                    }
                } else {
                    self.errors.push(TypeError::ResourceViolation {
                        span: provision.span,
                        message: format!("unknown unit '{}'", unit_name),
                        hint: Some("check the spelling of the unit".to_string()),
                    });
                }
            }
        }
    }

    /// Unify two types.
    fn unify(&mut self, t1: &Ty, t2: &Ty, span: eclexia_ast::span::Span) -> Result<(), TypeError> {
        // Delegate to unify_with_occurs_check for proper infinite type detection
        self.unify_with_occurs_check(t1, t2, span)
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
            Ty::Resource { base, dimension } => Ty::Resource {
                base: *base,
                dimension: *dimension,
            },
            _ => ty.clone(),
        }
    }
}

/// Type check a source file.
pub fn check(file: &SourceFile) -> Vec<TypeError> {
    let mut checker = TypeChecker::new(file);
    checker.check_all()
}
