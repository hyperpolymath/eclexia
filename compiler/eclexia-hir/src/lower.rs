// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! AST to HIR lowering.
//!
//! This module transforms the surface syntax (AST) into the
//! high-level intermediate representation (HIR).

use crate::*;
use eclexia_ast::{self as ast, SourceFile};
use eclexia_ast::types::Ty;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

/// Lowering context
pub struct LoweringContext<'a> {
    /// Source AST file
    source: &'a SourceFile,
    /// HIR being built
    hir: HirFile,
    /// Map from AST local names to HIR local IDs
    locals: FxHashMap<SmolStr, LocalId>,
    /// Type information from type checker
    types: FxHashMap<ast::ExprId, Ty>,
}

impl<'a> LoweringContext<'a> {
    /// Create a new lowering context
    pub fn new(source: &'a SourceFile) -> Self {
        Self {
            source,
            hir: HirFile::new(),
            locals: FxHashMap::default(),
            types: FxHashMap::default(),
        }
    }

    /// Set type information for expressions
    pub fn with_types(mut self, types: FxHashMap<ast::ExprId, Ty>) -> Self {
        self.types = types;
        self
    }

    /// Get the type of an AST expression
    fn expr_type(&self, expr_id: ast::ExprId) -> Ty {
        // First check if we have a type from the type checker
        if let Some(ty) = self.types.get(&expr_id) {
            return ty.clone();
        }

        // Otherwise, infer simple types from literals
        let expr = &self.source.exprs[expr_id];
        match &expr.kind {
            ast::ExprKind::Literal(lit) => match lit {
                ast::Literal::Int(_) => Ty::Primitive(PrimitiveTy::Int),
                ast::Literal::Float(_) => Ty::Primitive(PrimitiveTy::Float),
                ast::Literal::Bool(_) => Ty::Primitive(PrimitiveTy::Bool),
                ast::Literal::String(_) => Ty::Primitive(PrimitiveTy::String),
                ast::Literal::Char(_) => Ty::Primitive(PrimitiveTy::Char),
                ast::Literal::Unit => Ty::Primitive(PrimitiveTy::Unit),
            },
            _ => Ty::Primitive(PrimitiveTy::Unit),
        }
    }

    /// Define a local variable
    fn define_local(&mut self, span: Span, name: SmolStr, ty: Ty, mutable: bool) -> LocalId {
        let local_id = self.hir.locals.alloc(Local {
            span,
            name: name.clone(),
            ty,
            mutable,
        });
        self.locals.insert(name, local_id);
        local_id
    }

    /// Lookup a local variable
    fn lookup_local(&self, name: &str) -> Option<LocalId> {
        self.locals.get(name).copied()
    }

    /// Lower an AST item
    fn lower_item(&mut self, item: &ast::Item) -> Item {
        match item {
            ast::Item::Function(func) => Item::Function(self.lower_function(func)),
            ast::Item::AdaptiveFunction(func) => {
                Item::AdaptiveFunction(self.lower_adaptive_function(func))
            }
            ast::Item::TypeDef(typedef) => Item::TypeDef(self.lower_typedef(typedef)),
            ast::Item::Const(c) => Item::Const(self.lower_const(c)),
            ast::Item::Import(_) | ast::Item::EffectDecl(_) | ast::Item::ExternBlock(_) => {
                Item::Const(Const {
                    span: Span::default(),
                    name: SmolStr::new("_placeholder"),
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    value: self.hir.exprs.alloc(Expr {
                        span: Span::default(),
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ExprKind::Literal(Literal::Unit),
                    }),
                })
            }
            ast::Item::TraitDecl(t) => {
                Item::TraitDecl {
                    span: t.span,
                    name: t.name.clone(),
                }
            }
            ast::Item::ImplBlock(i) => {
                // Extract self type name
                let self_ty_name = match &self.source.types[i.self_ty].kind {
                    ast::TypeKind::Named { name, .. } => name.clone(),
                    _ => SmolStr::new("_"),
                };
                Item::ImplBlock {
                    span: i.span,
                    self_ty_name,
                }
            }
            ast::Item::ModuleDecl(m) => {
                let mod_items: Vec<Item> = m.items.as_ref()
                    .map(|items| items.iter().map(|item| self.lower_item(item)).collect())
                    .unwrap_or_default();
                Item::Module {
                    span: m.span,
                    name: m.name.clone(),
                    items: mod_items,
                }
            }
            ast::Item::StaticDecl(s) => {
                let value = self.lower_expr(s.value);
                let ty = self.convert_type(&self.source.types[s.ty]);
                Item::Static {
                    span: s.span,
                    name: s.name.clone(),
                    ty,
                    value,
                    mutable: s.mutable,
                }
            }
        }
    }

    /// Lower a function
    fn lower_function(&mut self, func: &ast::Function) -> Function {
        // Save parent scope
        let parent_locals = self.locals.clone();

        // Lower parameters
        let params: Vec<Param> = func
            .params
            .iter()
            .map(|p| {
                let ty = if let Some(ty_id) = p.ty {
                    self.convert_type(&self.source.types[ty_id])
                } else {
                    Ty::Primitive(PrimitiveTy::Unit)
                };
                let local = self.define_local(p.span, p.name.clone(), ty.clone(), false);
                Param {
                    span: p.span,
                    name: p.name.clone(),
                    ty,
                    local,
                }
            })
            .collect();

        // Lower return type
        let return_ty = if let Some(ty_id) = func.return_type {
            self.convert_type(&self.source.types[ty_id])
        } else {
            Ty::Primitive(PrimitiveTy::Unit)
        };

        // Lower constraints
        let constraints = self.lower_constraints(&func.constraints);

        // Lower body
        let body = self.lower_block(&func.body);

        // Restore parent scope
        self.locals = parent_locals;

        Function {
            span: func.span,
            name: func.name.clone(),
            params,
            return_ty,
            constraints,
            body,
        }
    }

    /// Lower an adaptive function
    fn lower_adaptive_function(&mut self, func: &ast::AdaptiveFunction) -> AdaptiveFunction {
        // Save parent scope
        let parent_locals = self.locals.clone();

        // Lower parameters
        let params: Vec<Param> = func
            .params
            .iter()
            .map(|p| {
                let ty = if let Some(ty_id) = p.ty {
                    self.convert_type(&self.source.types[ty_id])
                } else {
                    Ty::Primitive(PrimitiveTy::Unit)
                };
                let local = self.define_local(p.span, p.name.clone(), ty.clone(), false);
                Param {
                    span: p.span,
                    name: p.name.clone(),
                    ty,
                    local,
                }
            })
            .collect();

        // Lower return type
        let return_ty = if let Some(ty_id) = func.return_type {
            self.convert_type(&self.source.types[ty_id])
        } else {
            Ty::Primitive(PrimitiveTy::Unit)
        };

        // Lower constraints and objectives
        let constraints = self.lower_constraints(&func.constraints);
        let optimize = self.lower_objectives(&func.optimize);

        // Lower solutions
        let solutions: Vec<Solution> = func
            .solutions
            .iter()
            .map(|sol| {
                let when_clause = sol.when_clause.map(|e| self.lower_expr(e));
                let provides = self.lower_provisions(&sol.provides);
                let body = self.lower_block(&sol.body);

                Solution {
                    span: sol.span,
                    name: sol.name.clone(),
                    when_clause,
                    provides,
                    body,
                }
            })
            .collect();

        // Restore parent scope
        self.locals = parent_locals;

        AdaptiveFunction {
            span: func.span,
            name: func.name.clone(),
            params,
            return_ty,
            constraints,
            optimize,
            solutions,
        }
    }

    /// Lower resource constraints
    fn lower_constraints(&self, constraints: &[ast::Constraint]) -> Vec<ResourceConstraint> {
        constraints
            .iter()
            .filter_map(|c| match &c.kind {
                ast::ConstraintKind::Resource {
                    resource,
                    op,
                    amount,
                } => {
                    let dimension = self.resource_dimension(resource.as_str());
                    Some(ResourceConstraint {
                        span: c.span,
                        resource: resource.clone(),
                        dimension,
                        op: self.convert_constraint_op(*op),
                        bound: amount.value,
                        unit: amount.unit.clone(),
                    })
                }
                ast::ConstraintKind::Predicate(_) => None, // Handled elsewhere
            })
            .collect()
    }

    /// Lower resource provisions
    fn lower_provisions(&self, provisions: &[ast::ResourceProvision]) -> Vec<ResourceProvision> {
        provisions
            .iter()
            .map(|p| {
                let dimension = self.resource_dimension(p.resource.as_str());
                ResourceProvision {
                    span: p.span,
                    resource: p.resource.clone(),
                    dimension,
                    amount: p.amount.value,
                    unit: p.amount.unit.clone(),
                }
            })
            .collect()
    }

    /// Lower optimization objectives
    fn lower_objectives(&self, objectives: &[ast::Objective]) -> Vec<Objective> {
        objectives
            .iter()
            .map(|obj| Objective {
                span: obj.span,
                direction: match obj.direction {
                    ast::OptimizeDirection::Minimize => OptimizeDirection::Minimize,
                    ast::OptimizeDirection::Maximize => OptimizeDirection::Maximize,
                },
                target: obj.target.clone(),
            })
            .collect()
    }

    /// Get dimension for a resource name
    fn resource_dimension(&self, resource: &str) -> Dimension {
        match resource {
            "energy" => Dimension::energy(),
            "time" => Dimension::time(),
            "memory" => Dimension::memory(),
            "carbon" => Dimension::carbon(),
            "power" => Dimension::power(),
            _ => Dimension::dimensionless(),
        }
    }

    /// Convert constraint operator
    fn convert_constraint_op(&self, op: ast::CompareOp) -> ConstraintOp {
        match op {
            ast::CompareOp::Lt => ConstraintOp::Lt,
            ast::CompareOp::Le => ConstraintOp::Le,
            ast::CompareOp::Gt => ConstraintOp::Gt,
            ast::CompareOp::Ge => ConstraintOp::Ge,
            ast::CompareOp::Eq => ConstraintOp::Eq,
            ast::CompareOp::Ne => ConstraintOp::Ne,
        }
    }

    /// Lower a type definition
    fn lower_typedef(&mut self, typedef: &ast::TypeDef) -> TypeDef {
        let kind = match &typedef.kind {
            ast::TypeDefKind::Struct(fields) => TypeDefKind::Struct {
                fields: fields
                    .iter()
                    .map(|f| Field {
                        span: f.span,
                        name: f.name.clone(),
                        ty: self.convert_type(&self.source.types[f.ty]),
                    })
                    .collect(),
            },
            ast::TypeDefKind::Enum(variants) => TypeDefKind::Enum {
                variants: variants
                    .iter()
                    .map(|v| Variant {
                        span: v.span,
                        name: v.name.clone(),
                        fields: v
                            .fields
                            .as_ref()
                            .map(|flds| flds.iter().map(|&ty_id| self.convert_type(&self.source.types[ty_id])).collect())
                            .unwrap_or_default(),
                    })
                    .collect(),
            },
            ast::TypeDefKind::Alias(target) => TypeDefKind::Alias {
                target: self.convert_type(&self.source.types[*target]),
            },
        };

        TypeDef {
            span: typedef.span,
            name: typedef.name.clone(),
            kind,
        }
    }

    /// Lower a constant
    fn lower_const(&mut self, c: &ast::ConstDef) -> Const {
        let value = self.lower_expr(c.value);
        let ty = self.hir.exprs[value].ty.clone();

        Const {
            span: c.span,
            name: c.name.clone(),
            ty,
            value,
        }
    }

    /// Lower a block
    fn lower_block(&mut self, block: &ast::Block) -> Body {
        let stmts: Vec<StmtId> = block
            .stmts
            .iter()
            .map(|&stmt_id| self.lower_stmt(stmt_id))
            .collect();

        let expr = block.expr.map(|e| self.lower_expr(e));

        Body { stmts, expr }
    }

    /// Lower a statement
    fn lower_stmt(&mut self, stmt_id: ast::StmtId) -> StmtId {
        let stmt = &self.source.stmts[stmt_id];

        let kind = match &stmt.kind {
            ast::StmtKind::Let { ref pattern, mutable, ty, value } => {
                let init = Some(self.lower_expr(*value));
                let var_ty = if let Some(ty_id) = ty {
                    self.convert_type(&self.source.types[*ty_id])
                } else if let Some(init_id) = init {
                    self.hir.exprs[init_id].ty.clone()
                } else {
                    Ty::Primitive(PrimitiveTy::Unit)
                };

                // Lower pattern bindings
                match pattern {
                    ast::Pattern::Var(name) => {
                        let local = self.define_local(stmt.span, name.clone(), var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                    ast::Pattern::Wildcard | ast::Pattern::Rest => {
                        // Discard: bind to _ but still evaluate init
                        let local = self.define_local(stmt.span, SmolStr::new("_"), var_ty, false);
                        StmtKind::Let { local, init }
                    }
                    ast::Pattern::Tuple(pats) => {
                        // let (a, b) = expr → let _tup = expr; let a = _tup.0; let b = _tup.1
                        let tup_local = self.define_local(stmt.span, SmolStr::new("_tup"), var_ty.clone(), false);
                        let tup_let = self.hir.stmts.alloc(Stmt {
                            span: stmt.span,
                            kind: StmtKind::Let { local: tup_local, init },
                        });
                        // Emit element bindings as expr stmts; return tup_let
                        for (i, pat) in pats.iter().enumerate() {
                            if let ast::Pattern::Var(name) = pat {
                                let elem_ty = match &var_ty {
                                    Ty::Tuple(elems) => elems.get(i).cloned().unwrap_or(Ty::Primitive(PrimitiveTy::Unit)),
                                    _ => Ty::Primitive(PrimitiveTy::Unit),
                                };
                                let tup_ref = self.hir.exprs.alloc(Expr {
                                    span: stmt.span,
                                    ty: var_ty.clone(),
                                    kind: ExprKind::Local(tup_local),
                                });
                                let field_expr = self.hir.exprs.alloc(Expr {
                                    span: stmt.span,
                                    ty: elem_ty.clone(),
                                    kind: ExprKind::Field {
                                        expr: tup_ref,
                                        field: SmolStr::new(i.to_string()),
                                    },
                                });
                                let elem_local = self.define_local(stmt.span, name.clone(), elem_ty, *mutable);
                                self.hir.stmts.alloc(Stmt {
                                    span: stmt.span,
                                    kind: StmtKind::Let { local: elem_local, init: Some(field_expr) },
                                });
                            }
                        }
                        return tup_let;
                    }
                    ast::Pattern::Binding { name, .. } => {
                        // name @ pattern: bind the whole value to name
                        let local = self.define_local(stmt.span, name.clone(), var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                    ast::Pattern::Reference { pattern: inner, .. } => {
                        // &pat: bind inner pattern name
                        let name = self.extract_pattern_name(inner);
                        let local = self.define_local(stmt.span, name, var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                    ast::Pattern::Constructor { name, .. } => {
                        // Constructor pattern in let: bind to constructor name as variable
                        let local = self.define_local(stmt.span, name.clone(), var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                    ast::Pattern::Struct { name, .. } => {
                        let local = self.define_local(stmt.span, name.clone(), var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                    _ => {
                        // Literal, Slice, Or, Range patterns: bind to _
                        let local = self.define_local(stmt.span, SmolStr::new("_"), var_ty, *mutable);
                        StmtKind::Let { local, init }
                    }
                }
            }
            ast::StmtKind::Assign { target, value } => {
                let value_expr = self.lower_expr(*value);
                let place = self.lower_place(*target);

                StmtKind::Assign {
                    place,
                    value: value_expr,
                }
            }
            ast::StmtKind::Expr(e) => StmtKind::Expr(self.lower_expr(*e)),
            ast::StmtKind::Return(e) => StmtKind::Return(e.map(|e| self.lower_expr(e))),
            ast::StmtKind::Loop { label, body } => {
                let body = self.lower_block(body);
                StmtKind::InfiniteLoop {
                    label: label.clone(),
                    body,
                }
            }
            ast::StmtKind::Break { label, value } => {
                StmtKind::Break {
                    label: label.clone(),
                    value: value.map(|v| self.lower_expr(v)),
                }
            }
            ast::StmtKind::Continue { label } => {
                StmtKind::Continue {
                    label: label.clone(),
                }
            }
            ast::StmtKind::While { condition, body } => {
                let cond_id = self.lower_expr(*condition);
                let body = self.lower_block(body);
                let loop_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Loop {
                        condition: cond_id,
                        body,
                    },
                });
                StmtKind::Expr(loop_expr)
            }
            ast::StmtKind::For { ref pattern, iter, body } => {
                let name = self.extract_pattern_name(pattern);

                // Desugar: for x in array { body } =>
                //   let _iter = array
                //   let _i = 0
                //   while _i < len(_iter) {
                //     let x = _iter[_i]
                //     body stmts...
                //     _i = _i + 1
                //   }

                let iter_expr = self.lower_expr(*iter);
                let iter_ty = self.hir.exprs[iter_expr].ty.clone();

                // let _iter = <iter_expr>
                let iter_local = self.define_local(
                    stmt.span,
                    SmolStr::new("_iter"),
                    iter_ty.clone(),
                    false,
                );
                let iter_let_stmt = self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Let { local: iter_local, init: Some(iter_expr) },
                });

                // let _i = 0
                let idx_local = self.define_local(
                    stmt.span,
                    SmolStr::new("_i"),
                    Ty::Primitive(PrimitiveTy::Int),
                    true,
                );
                let zero = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Literal(Literal::Int(0)),
                });
                let idx_let_stmt = self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Let { local: idx_local, init: Some(zero) },
                });

                // Determine element type
                let elem_ty = match &iter_ty {
                    Ty::Array { elem, .. } => (**elem).clone(),
                    _ => Ty::Primitive(PrimitiveTy::Unit),
                };

                // Build condition: _i < len(_iter)
                // Use _iter.len field access as simplified length
                let iter_ref = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: iter_ty.clone(),
                    kind: ExprKind::Local(iter_local),
                });
                let len_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Field {
                        expr: iter_ref,
                        field: SmolStr::new("len"),
                    },
                });
                let idx_ref = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Local(idx_local),
                });
                let condition = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Bool),
                    kind: ExprKind::Binary {
                        op: BinaryOp::Lt,
                        lhs: idx_ref,
                        rhs: len_expr,
                    },
                });

                // Build loop body: let x = _iter[_i]; <original body stmts>; _i = _i + 1
                // Element binding: let x = _iter[_i]
                let iter_ref2 = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: iter_ty.clone(),
                    kind: ExprKind::Local(iter_local),
                });
                let idx_ref2 = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Local(idx_local),
                });
                let elem_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: elem_ty.clone(),
                    kind: ExprKind::Index {
                        expr: iter_ref2,
                        index: idx_ref2,
                    },
                });
                let elem_local = self.define_local(stmt.span, name, elem_ty, false);
                let elem_let = self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Let { local: elem_local, init: Some(elem_expr) },
                });

                // Lower original body
                let original_body = self.lower_block(body);

                // Increment: _i = _i + 1
                let idx_ref3 = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Local(idx_local),
                });
                let one = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Literal(Literal::Int(1)),
                });
                let inc_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Int),
                    kind: ExprKind::Binary {
                        op: BinaryOp::Add,
                        lhs: idx_ref3,
                        rhs: one,
                    },
                });
                let inc_assign = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Assign {
                        target: idx_local,
                        value: inc_expr,
                    },
                });
                let inc_stmt = self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Expr(inc_assign),
                });

                // Combine: [elem_let, original body stmts..., inc_stmt]
                let mut loop_stmts = vec![elem_let];
                loop_stmts.extend(original_body.stmts);
                loop_stmts.push(inc_stmt);

                let while_body = Body {
                    stmts: loop_stmts,
                    expr: original_body.expr,
                };

                let while_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Loop {
                        condition,
                        body: while_body,
                    },
                });

                // Wrap in a block: { let _iter = ...; let _i = 0; while ... }
                let while_stmt = self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Expr(while_expr),
                });

                let block_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Block(Body {
                        stmts: vec![iter_let_stmt, idx_let_stmt, while_stmt],
                        expr: None,
                    }),
                });

                StmtKind::Expr(block_expr)
            }
        };

        self.hir.stmts.alloc(Stmt {
            span: stmt.span,
            kind,
        })
    }

    /// Lower an expression
    fn lower_expr(&mut self, expr_id: ast::ExprId) -> ExprId {
        let expr = &self.source.exprs[expr_id];
        let ty = self.expr_type(expr_id);

        let kind = match &expr.kind {
            ast::ExprKind::Literal(lit) => ExprKind::Literal(self.lower_literal(lit)),

            ast::ExprKind::Var(name) => {
                if let Some(local_id) = self.lookup_local(name.as_str()) {
                    ExprKind::Local(local_id)
                } else {
                    // Not a local variable - might be a function name
                    // Create a placeholder local for it (will be resolved in MIR)
                    let local_id = self.define_local(expr.span, name.clone(), Ty::Primitive(PrimitiveTy::Unit), false);
                    ExprKind::Local(local_id)
                }
            }

            ast::ExprKind::Binary { op, lhs, rhs } => {
                let lhs_id = self.lower_expr(*lhs);
                let rhs_id = self.lower_expr(*rhs);
                ExprKind::Binary {
                    op: (*op).into(),
                    lhs: lhs_id,
                    rhs: rhs_id,
                }
            }

            ast::ExprKind::Unary { op, operand } => {
                let operand_id = self.lower_expr(*operand);
                ExprKind::Unary {
                    op: (*op).into(),
                    operand: operand_id,
                }
            }

            ast::ExprKind::Call { func, args } => {
                let func_id = self.lower_expr(*func);
                let arg_ids: Vec<ExprId> = args.iter().map(|&a| self.lower_expr(a)).collect();
                ExprKind::Call {
                    func: func_id,
                    args: arg_ids,
                }
            }

            ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond_id = self.lower_expr(*condition);
                let then_body = self.lower_block(then_branch);
                let else_body = else_branch.as_ref().map(|b| self.lower_block(b));
                ExprKind::If {
                    condition: cond_id,
                    then_branch: then_body,
                    else_branch: else_body,
                }
            }

            ast::ExprKind::Block(block) => ExprKind::Block(self.lower_block(block)),

            ast::ExprKind::Tuple(elems) => {
                let elem_ids: Vec<ExprId> = elems.iter().map(|&e| self.lower_expr(e)).collect();
                ExprKind::Tuple(elem_ids)
            }

            ast::ExprKind::Array(elems) => {
                let elem_ids: Vec<ExprId> = elems.iter().map(|&e| self.lower_expr(e)).collect();
                ExprKind::Array(elem_ids)
            }

            ast::ExprKind::Index { expr: arr, index } => {
                let arr_id = self.lower_expr(*arr);
                let idx_id = self.lower_expr(*index);
                ExprKind::Index {
                    expr: arr_id,
                    index: idx_id,
                }
            }

            ast::ExprKind::Field { expr: obj, field } => {
                let obj_id = self.lower_expr(*obj);
                ExprKind::Field {
                    expr: obj_id,
                    field: field.clone(),
                }
            }

            ast::ExprKind::Lambda { params, body } => {
                let parent_locals = self.locals.clone();

                let hir_params: Vec<Param> = params
                    .iter()
                    .map(|p| {
                        let param_ty = if let Some(ty_id) = p.ty {
                            self.convert_type(&self.source.types[ty_id])
                        } else {
                            Ty::Primitive(PrimitiveTy::Unit)
                        };
                        let local = self.define_local(p.span, p.name.clone(), param_ty.clone(), false);
                        Param {
                            span: p.span,
                            name: p.name.clone(),
                            ty: param_ty,
                            local,
                        }
                    })
                    .collect();

                let lambda_body = self.lower_expr(*body);
                let body = Body {
                    stmts: vec![],
                    expr: Some(lambda_body),
                };

                self.locals = parent_locals;

                ExprKind::Lambda {
                    params: hir_params,
                    body,
                }
            }

            ast::ExprKind::Match { scrutinee, arms } => {
                // Desugar match to if-else chain:
                //   match x { A => a, B => b, _ => c }
                //   =>
                //   let _scrut = x;
                //   if _scrut == A { a } else if _scrut == B { b } else { c }

                let scrut_expr = self.lower_expr(*scrutinee);
                let scrut_ty = self.hir.exprs[scrut_expr].ty.clone();
                let scrut_local = self.define_local(expr.span, SmolStr::new("_scrut"), scrut_ty.clone(), false);
                let scrut_let = self.hir.stmts.alloc(Stmt {
                    span: expr.span,
                    kind: StmtKind::Let { local: scrut_local, init: Some(scrut_expr) },
                });

                // Build if-else chain from arms (in reverse to nest else branches)
                let result = self.lower_match_arms(expr.span, scrut_local, arms, &ty);

                // Wrap: { let _scrut = x; <if-else chain> }
                let block_expr = self.hir.exprs.alloc(Expr {
                    span: expr.span,
                    ty: ty.clone(),
                    kind: ExprKind::Block(Body {
                        stmts: vec![scrut_let],
                        expr: Some(result),
                    }),
                });
                return block_expr;
            }

            ast::ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                // Desugar: receiver.method(args) → method(receiver, args)
                let recv_id = self.lower_expr(*receiver);
                let mut all_args = vec![recv_id];
                all_args.extend(args.iter().map(|&a| self.lower_expr(a)));

                // Create a local for the method name (resolved in later passes)
                let method_local = self.define_local(
                    expr.span,
                    method.clone(),
                    Ty::Primitive(PrimitiveTy::Unit),
                    false,
                );
                let func_id = self.hir.exprs.alloc(Expr {
                    span: expr.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Local(method_local),
                });

                ExprKind::Call {
                    func: func_id,
                    args: all_args,
                }
            }

            ast::ExprKind::Struct { name, fields } => {
                let field_exprs: Vec<(SmolStr, ExprId)> = fields
                    .iter()
                    .map(|(n, e)| (n.clone(), self.lower_expr(*e)))
                    .collect();
                ExprKind::Struct {
                    name: name.clone(),
                    fields: field_exprs,
                }
            }

            ast::ExprKind::Resource(amount) => {
                // Parse the unit to get dimension
                let dimension = if let Some(unit_name) = &amount.unit {
                    if let Some(unit) = ast::dimension::parse_unit(unit_name.as_str()) {
                        unit.dimension
                    } else {
                        Dimension::dimensionless()
                    }
                } else {
                    Dimension::dimensionless()
                };

                ExprKind::Literal(Literal::Resource {
                    value: amount.value,
                    dimension,
                    unit: amount.unit.clone(),
                })
            }

            ast::ExprKind::Cast { expr, target_ty } => {
                let inner = self.lower_expr(*expr);
                let ty = self.convert_type(&self.source.types[*target_ty]);
                return self.hir.exprs.alloc(Expr {
                    span: self.source.exprs[expr_id].span,
                    ty: ty.clone(),
                    kind: ExprKind::Cast {
                        expr: inner,
                        target_ty: ty,
                    },
                });
            }
            ast::ExprKind::ArrayRepeat { value, count } => {
                let val = self.lower_expr(*value);
                let cnt = self.lower_expr(*count);
                ExprKind::ArrayRepeat { value: val, count: cnt }
            }
            ast::ExprKind::Try(inner) => {
                let inner_id = self.lower_expr(*inner);
                ExprKind::Try(inner_id)
            }
            ast::ExprKind::Borrow { expr: inner, mutable } => {
                let inner_id = self.lower_expr(*inner);
                ExprKind::Borrow { expr: inner_id, mutable: *mutable }
            }
            ast::ExprKind::Deref(inner) => {
                let inner_id = self.lower_expr(*inner);
                ExprKind::Deref(inner_id)
            }
            ast::ExprKind::AsyncBlock(block) => {
                ExprKind::Block(self.lower_block(block))
            }
            ast::ExprKind::Await(inner) => {
                let inner_id = self.lower_expr(*inner);
                return inner_id;
            }
            ast::ExprKind::Handle { expr: inner, .. } => {
                let inner_id = self.lower_expr(*inner);
                return inner_id;
            }
            ast::ExprKind::ReturnExpr(val) => {
                ExprKind::ReturnExpr(val.map(|v| self.lower_expr(v)))
            }
            ast::ExprKind::BreakExpr { label, value } => {
                ExprKind::BreakExpr {
                    label: label.clone(),
                    value: value.map(|v| self.lower_expr(v)),
                }
            }
            ast::ExprKind::ContinueExpr { label } => {
                ExprKind::ContinueExpr {
                    label: label.clone(),
                }
            }
            ast::ExprKind::PathExpr(segments) => {
                // Treat path as a variable reference to the last segment
                let name = segments.last().cloned().unwrap_or_else(|| SmolStr::new("_"));
                if let Some(local_id) = self.lookup_local(name.as_str()) {
                    ExprKind::Local(local_id)
                } else {
                    let local_id = self.define_local(expr.span, name, Ty::Primitive(PrimitiveTy::Unit), false);
                    ExprKind::Local(local_id)
                }
            }
            ast::ExprKind::Error => ExprKind::Literal(Literal::Unit),
        };

        self.hir.exprs.alloc(Expr {
            span: expr.span,
            ty,
            kind,
        })
    }

    /// Lower a literal
    fn lower_literal(&self, lit: &ast::Literal) -> Literal {
        match lit {
            ast::Literal::Int(i) => Literal::Int(*i),
            ast::Literal::Float(f) => Literal::Float(*f),
            ast::Literal::String(s) => Literal::String(s.clone()),
            ast::Literal::Char(c) => Literal::Char(*c),
            ast::Literal::Bool(b) => Literal::Bool(*b),
            ast::Literal::Unit => Literal::Unit,
        }
    }

    /// Extract a binding name from a pattern
    fn extract_pattern_name(&self, pattern: &ast::Pattern) -> SmolStr {
        match pattern {
            ast::Pattern::Var(name) => name.clone(),
            ast::Pattern::Binding { name, .. } => name.clone(),
            ast::Pattern::Reference { pattern: inner, .. } => self.extract_pattern_name(inner),
            _ => SmolStr::new("_"),
        }
    }

    /// Lower an AST expression to a HIR Place (lvalue)
    fn lower_place(&mut self, expr_id: ast::ExprId) -> Place {
        let expr = &self.source.exprs[expr_id];
        match &expr.kind {
            ast::ExprKind::Var(name) => {
                let local_id = if let Some(id) = self.lookup_local(name.as_str()) {
                    id
                } else {
                    self.define_local(expr.span, name.clone(), Ty::Primitive(PrimitiveTy::Unit), true)
                };
                Place::Local(local_id)
            }
            ast::ExprKind::Field { expr: base, field } => {
                let base_place = self.lower_place(*base);
                Place::Field {
                    base: Box::new(base_place),
                    field: field.clone(),
                }
            }
            ast::ExprKind::Index { expr: base, index } => {
                let base_place = self.lower_place(*base);
                let index_expr = self.lower_expr(*index);
                Place::Index {
                    base: Box::new(base_place),
                    index: index_expr,
                }
            }
            ast::ExprKind::Deref(inner) => {
                // *ptr = value → treat as local assignment through deref
                self.lower_place(*inner)
            }
            _ => {
                // Fallback: evaluate as expr, assign to temp
                let local = self.define_local(expr.span, SmolStr::new("_assign"), Ty::Primitive(PrimitiveTy::Unit), true);
                Place::Local(local)
            }
        }
    }

    /// Lower match arms to an if-else chain expression
    fn lower_match_arms(
        &mut self,
        span: Span,
        scrut_local: LocalId,
        arms: &[ast::MatchArm],
        result_ty: &Ty,
    ) -> ExprId {
        if arms.is_empty() {
            // No arms: return unit
            return self.hir.exprs.alloc(Expr {
                span,
                ty: result_ty.clone(),
                kind: ExprKind::Literal(Literal::Unit),
            });
        }

        let arm = &arms[0];
        let arm_body = self.lower_expr(arm.body);

        // Check if this is a wildcard/catch-all pattern
        if self.is_wildcard_pattern(&arm.pattern) {
            // Wildcard: just return the body (possibly bind variable first)
            if let ast::Pattern::Var(name) = &arm.pattern {
                let scrut_ref = self.hir.exprs.alloc(Expr {
                    span: arm.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Local(scrut_local),
                });
                let _local = self.define_local(arm.span, name.clone(), Ty::Primitive(PrimitiveTy::Unit), false);
                let bind_stmt = self.hir.stmts.alloc(Stmt {
                    span: arm.span,
                    kind: StmtKind::Let { local: _local, init: Some(scrut_ref) },
                });
                return self.hir.exprs.alloc(Expr {
                    span: arm.span,
                    ty: result_ty.clone(),
                    kind: ExprKind::Block(Body {
                        stmts: vec![bind_stmt],
                        expr: Some(arm_body),
                    }),
                });
            }
            return arm_body;
        }

        // Build condition from pattern
        let condition = self.lower_pattern_condition(arm.span, scrut_local, &arm.pattern);

        // Apply guard if present
        let final_condition = if let Some(guard) = arm.guard {
            let guard_expr = self.lower_expr(guard);
            self.hir.exprs.alloc(Expr {
                span: arm.span,
                ty: Ty::Primitive(PrimitiveTy::Bool),
                kind: ExprKind::Binary {
                    op: BinaryOp::And,
                    lhs: condition,
                    rhs: guard_expr,
                },
            })
        } else {
            condition
        };

        // Build then branch (may include pattern bindings)
        let then_body = Body {
            stmts: vec![],
            expr: Some(arm_body),
        };

        // Build else branch from remaining arms
        let else_body = if arms.len() > 1 {
            let rest = self.lower_match_arms(span, scrut_local, &arms[1..], result_ty);
            Some(Body {
                stmts: vec![],
                expr: Some(rest),
            })
        } else {
            None
        };

        self.hir.exprs.alloc(Expr {
            span: arm.span,
            ty: result_ty.clone(),
            kind: ExprKind::If {
                condition: final_condition,
                then_branch: then_body,
                else_branch: else_body,
            },
        })
    }

    /// Check if a pattern is a wildcard/catch-all
    fn is_wildcard_pattern(&self, pattern: &ast::Pattern) -> bool {
        matches!(pattern, ast::Pattern::Wildcard | ast::Pattern::Var(_) | ast::Pattern::Rest)
    }

    /// Lower a pattern to a boolean condition expression
    fn lower_pattern_condition(
        &mut self,
        span: Span,
        scrut_local: LocalId,
        pattern: &ast::Pattern,
    ) -> ExprId {
        let scrut_ref = self.hir.exprs.alloc(Expr {
            span,
            ty: Ty::Primitive(PrimitiveTy::Unit),
            kind: ExprKind::Local(scrut_local),
        });

        match pattern {
            ast::Pattern::Literal(lit) => {
                // scrutinee == literal
                let lit_expr = self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Literal(self.lower_literal(lit)),
                });
                self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Bool),
                    kind: ExprKind::Binary {
                        op: BinaryOp::Eq,
                        lhs: scrut_ref,
                        rhs: lit_expr,
                    },
                })
            }
            ast::Pattern::Constructor { name, .. } => {
                // scrutinee == ConstructorName (tag comparison)
                let tag_local = self.define_local(span, name.clone(), Ty::Primitive(PrimitiveTy::Unit), false);
                let tag_ref = self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Local(tag_local),
                });
                self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Bool),
                    kind: ExprKind::Binary {
                        op: BinaryOp::Eq,
                        lhs: scrut_ref,
                        rhs: tag_ref,
                    },
                })
            }
            ast::Pattern::Or(alternatives) => {
                // pat1 | pat2 → condition1 || condition2
                if alternatives.is_empty() {
                    return self.hir.exprs.alloc(Expr {
                        span,
                        ty: Ty::Primitive(PrimitiveTy::Bool),
                        kind: ExprKind::Literal(Literal::Bool(false)),
                    });
                }
                let mut result = self.lower_pattern_condition(span, scrut_local, &alternatives[0]);
                for alt in &alternatives[1..] {
                    let alt_cond = self.lower_pattern_condition(span, scrut_local, alt);
                    result = self.hir.exprs.alloc(Expr {
                        span,
                        ty: Ty::Primitive(PrimitiveTy::Bool),
                        kind: ExprKind::Binary {
                            op: BinaryOp::Or,
                            lhs: result,
                            rhs: alt_cond,
                        },
                    });
                }
                result
            }
            ast::Pattern::Range { start, end, inclusive } => {
                // start..=end → scrutinee >= start && scrutinee <= end
                let mut conditions = vec![];
                if let Some(start_pat) = start {
                    if let ast::Pattern::Literal(lit) = start_pat.as_ref() {
                        let start_expr = self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Unit),
                            kind: ExprKind::Literal(self.lower_literal(lit)),
                        });
                        let scrut_ref2 = self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Unit),
                            kind: ExprKind::Local(scrut_local),
                        });
                        conditions.push(self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Bool),
                            kind: ExprKind::Binary {
                                op: BinaryOp::Ge,
                                lhs: scrut_ref2,
                                rhs: start_expr,
                            },
                        }));
                    }
                }
                if let Some(end_pat) = end {
                    if let ast::Pattern::Literal(lit) = end_pat.as_ref() {
                        let end_expr = self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Unit),
                            kind: ExprKind::Literal(self.lower_literal(lit)),
                        });
                        let scrut_ref3 = self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Unit),
                            kind: ExprKind::Local(scrut_local),
                        });
                        let op = if *inclusive { BinaryOp::Le } else { BinaryOp::Lt };
                        conditions.push(self.hir.exprs.alloc(Expr {
                            span,
                            ty: Ty::Primitive(PrimitiveTy::Bool),
                            kind: ExprKind::Binary {
                                op,
                                lhs: scrut_ref3,
                                rhs: end_expr,
                            },
                        }));
                    }
                }
                if conditions.is_empty() {
                    return self.hir.exprs.alloc(Expr {
                        span,
                        ty: Ty::Primitive(PrimitiveTy::Bool),
                        kind: ExprKind::Literal(Literal::Bool(true)),
                    });
                }
                let mut result = conditions[0];
                for cond in &conditions[1..] {
                    result = self.hir.exprs.alloc(Expr {
                        span,
                        ty: Ty::Primitive(PrimitiveTy::Bool),
                        kind: ExprKind::Binary {
                            op: BinaryOp::And,
                            lhs: result,
                            rhs: *cond,
                        },
                    });
                }
                result
            }
            ast::Pattern::Binding { pattern: inner, .. } => {
                // name @ pattern → check inner pattern
                self.lower_pattern_condition(span, scrut_local, inner)
            }
            ast::Pattern::Reference { pattern: inner, .. } => {
                self.lower_pattern_condition(span, scrut_local, inner)
            }
            ast::Pattern::Wildcard | ast::Pattern::Var(_) | ast::Pattern::Rest => {
                // Always matches
                self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Bool),
                    kind: ExprKind::Literal(Literal::Bool(true)),
                })
            }
            _ => {
                // Tuple, Struct, Slice patterns: simplified to true (full structural matching is complex)
                self.hir.exprs.alloc(Expr {
                    span,
                    ty: Ty::Primitive(PrimitiveTy::Bool),
                    kind: ExprKind::Literal(Literal::Bool(true)),
                })
            }
        }
    }

    /// Convert an AST type to a semantic type
    fn convert_type(&self, ty: &ast::Type) -> Ty {
        match &ty.kind {
            ast::TypeKind::Named { name, args } => {
                if args.is_empty() {
                    match name.as_str() {
                        "Int" => Ty::Primitive(PrimitiveTy::Int),
                        "Float" => Ty::Primitive(PrimitiveTy::Float),
                        "Bool" => Ty::Primitive(PrimitiveTy::Bool),
                        "String" => Ty::Primitive(PrimitiveTy::String),
                        "Char" => Ty::Primitive(PrimitiveTy::Char),
                        "Unit" => Ty::Primitive(PrimitiveTy::Unit),
                        _ => Ty::Named {
                            name: name.clone(),
                            args: vec![],
                        },
                    }
                } else {
                    let arg_tys: Vec<Ty> = args
                        .iter()
                        .map(|a| self.convert_type(&self.source.types[*a]))
                        .collect();
                    Ty::Named {
                        name: name.clone(),
                        args: arg_tys,
                    }
                }
            }
            ast::TypeKind::Array { elem, size } => {
                let elem_ty = self.convert_type(&self.source.types[*elem]);
                Ty::Array {
                    elem: Box::new(elem_ty),
                    size: *size,
                }
            }
            ast::TypeKind::Tuple(elems) => {
                let elem_tys: Vec<Ty> = elems
                    .iter()
                    .map(|e| self.convert_type(&self.source.types[*e]))
                    .collect();
                Ty::Tuple(elem_tys)
            }
            ast::TypeKind::Function { params, ret } => {
                let param_tys: Vec<Ty> = params
                    .iter()
                    .map(|p| self.convert_type(&self.source.types[*p]))
                    .collect();
                let ret_ty = self.convert_type(&self.source.types[*ret]);
                Ty::Function {
                    params: param_tys,
                    ret: Box::new(ret_ty),
                }
            }
            ast::TypeKind::Resource { base, dimension } => {
                let base_ty = match base.as_str() {
                    "Float" | "F64" => PrimitiveTy::Float,
                    "Int" | "I64" => PrimitiveTy::Int,
                    _ => PrimitiveTy::Float,
                };
                Ty::Resource {
                    base: base_ty,
                    dimension: *dimension,
                }
            }
            ast::TypeKind::Reference { ty, mutable } => {
                let inner_ty = self.convert_type(&self.source.types[*ty]);
                Ty::Named {
                    name: if *mutable { SmolStr::new("&mut") } else { SmolStr::new("&") },
                    args: vec![inner_ty],
                }
            }
            ast::TypeKind::Optional(inner) => {
                let inner_ty = self.convert_type(&self.source.types[*inner]);
                Ty::Named {
                    name: SmolStr::new("Option"),
                    args: vec![inner_ty],
                }
            }
            ast::TypeKind::Infer => Ty::Primitive(PrimitiveTy::Unit),
            ast::TypeKind::Error => Ty::Error,
        }
    }
}

/// Lower an AST source file to HIR
pub fn lower_source_file(source: &SourceFile) -> HirFile {
    let mut ctx = LoweringContext::new(source);

    let items: Vec<Item> = source.items.iter().map(|item| ctx.lower_item(item)).collect();

    ctx.hir.items = items;
    ctx.hir
}
