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
            ast::Item::Import(_) => {
                // Imports are already resolved, skip in HIR
                Item::Const(Const {
                    span: Span::default(),
                    name: SmolStr::new("_import"),
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    value: self.hir.exprs.alloc(Expr {
                        span: Span::default(),
                        ty: Ty::Primitive(PrimitiveTy::Unit),
                        kind: ExprKind::Literal(Literal::Unit),
                    }),
                })
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
            ast::StmtKind::Let { name, ty, value } => {
                let init = Some(self.lower_expr(*value));
                let var_ty = if let Some(ty_id) = ty {
                    self.convert_type(&self.source.types[*ty_id])
                } else if let Some(init_id) = init {
                    self.hir.exprs[init_id].ty.clone()
                } else {
                    Ty::Primitive(PrimitiveTy::Unit)
                };

                let local = self.define_local(stmt.span, name.clone(), var_ty, false);

                StmtKind::Let { local, init }
            }
            ast::StmtKind::Assign { target, value } => {
                // Look up the local variable
                let local = if let Some(local_id) = self.lookup_local(target.as_str()) {
                    local_id
                } else {
                    // Variable not found - create an error local
                    self.define_local(stmt.span, target.clone(), Ty::Primitive(PrimitiveTy::Unit), true)
                };

                let value_expr = self.lower_expr(*value);

                // Create an assignment expression
                let assign_expr = self.hir.exprs.alloc(Expr {
                    span: stmt.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Assign {
                        target: local,
                        value: value_expr,
                    },
                });

                StmtKind::Expr(assign_expr)
            }
            ast::StmtKind::Expr(e) => StmtKind::Expr(self.lower_expr(*e)),
            ast::StmtKind::Return(e) => StmtKind::Return(e.map(|e| self.lower_expr(e))),
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
            ast::StmtKind::For { name, iter, body } => {
                // Desugar: for x in array { body } =>
                //   let _iter = array
                //   let _i = 0
                //   while _i < len(_iter) {
                //     let x = _iter[_i]
                //     body
                //     _i = _i + 1
                //   }

                let iter_expr = self.lower_expr(*iter);
                let iter_ty = self.hir.exprs[iter_expr].ty.clone();

                // Create temporary for iterator
                let iter_local = self.define_local(
                    stmt.span,
                    SmolStr::new("_iter"),
                    iter_ty.clone(),
                    false,
                );

                // Create index variable
                let idx_local = self.define_local(
                    stmt.span,
                    SmolStr::new("_i"),
                    Ty::Primitive(PrimitiveTy::Int),
                    true,
                );

                // Lower loop body with element binding
                let elem_ty = match &iter_ty {
                    Ty::Array { elem, .. } => (**elem).clone(),
                    _ => Ty::Primitive(PrimitiveTy::Unit),
                };
                let elem_local = self.define_local(stmt.span, name.clone(), elem_ty, false);

                let loop_body = self.lower_block(body);

                // This is simplified - actual implementation would build full HIR
                return self.hir.stmts.alloc(Stmt {
                    span: stmt.span,
                    kind: StmtKind::Expr(iter_expr),
                });
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

            ast::ExprKind::Match { .. } => {
                // TODO: Desugar match to if-else chains
                ExprKind::Literal(Literal::Unit)
            }

            ast::ExprKind::MethodCall {
                receiver,
                method: _method,
                args,
            } => {
                // Desugar method calls to function calls
                let recv_id = self.lower_expr(*receiver);
                let mut all_args = vec![recv_id];
                all_args.extend(args.iter().map(|&a| self.lower_expr(a)));

                // Create function reference (simplified - should lookup in scope)
                let func_id = self.hir.exprs.alloc(Expr {
                    span: expr.span,
                    ty: Ty::Primitive(PrimitiveTy::Unit),
                    kind: ExprKind::Literal(Literal::Unit),
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
