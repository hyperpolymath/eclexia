// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Expression and statement evaluation.

use crate::builtins;
use crate::env::Environment;
use crate::error::{RuntimeError, RuntimeResult};
use crate::value::{AdaptiveFunction, Function, FunctionBody, ResourceProvides, ResourceRequires, Solution, Value};
use eclexia_ast::*;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::rc::Rc;

/// Maximum call depth to prevent stack overflow
const MAX_CALL_DEPTH: usize = 1000;

/// Maximum iterations per loop to prevent infinite loops
const MAX_LOOP_ITERATIONS: u64 = 10_000_000;

/// The Eclexia interpreter.
pub struct Interpreter {
    /// Global environment
    global: Environment,
    /// Current resource usage
    energy_used: f64,
    carbon_used: f64,
    /// Resource budgets
    energy_budget: f64,
    carbon_budget: f64,
    /// Shadow prices (simplified)
    shadow_energy: f64,
    shadow_carbon: f64,
    shadow_latency: f64,
    /// Current call depth for recursion limiting
    call_depth: usize,
}

impl Interpreter {
    /// Create a new interpreter with default settings.
    pub fn new() -> Self {
        let global = Environment::new();

        // Register built-in functions
        builtins::register(&global);

        Self {
            global,
            energy_used: 0.0,
            carbon_used: 0.0,
            energy_budget: 1000.0,  // Default 1000J
            carbon_budget: 100.0,   // Default 100gCO2e
            shadow_energy: 1.0,
            shadow_carbon: 1.0,
            shadow_latency: 1.0,
            call_depth: 0,
        }
    }

    /// Set the energy budget.
    pub fn set_energy_budget(&mut self, budget: f64) {
        self.energy_budget = budget;
    }

    /// Set the carbon budget.
    pub fn set_carbon_budget(&mut self, budget: f64) {
        self.carbon_budget = budget;
    }

    /// Run a source file.
    pub fn run(&mut self, file: &SourceFile) -> RuntimeResult<Value> {
        // First pass: register all top-level definitions
        for item in &file.items {
            self.register_item(item, file)?;
        }

        // Look for and call main()
        if let Some(main) = self.global.get("main") {
            self.call_value(&main, &[], file)
        } else {
            Ok(Value::Unit)
        }
    }

    /// Register a top-level item.
    fn register_item(&mut self, item: &Item, file: &SourceFile) -> RuntimeResult<()> {
        match item {
            Item::Function(func) => {
                let value = Value::Function(Rc::new(Function {
                    name: func.name.clone(),
                    params: func.params.iter().map(|p| p.name.clone()).collect(),
                    body: FunctionBody::Block {
                        file_idx: 0, // Simplified: single file
                        block_idx: 0,
                    },
                    closure: self.global.clone(),
                }));
                self.global.define(func.name.clone(), value);
            }
            Item::AdaptiveFunction(func) => {
                // Parse @requires constraints
                let mut requires = ResourceRequires::default();
                for constraint in &func.constraints {
                    if let ConstraintKind::Resource { resource, op, amount } = &constraint.kind {
                        // Only support < and <= for @requires
                        if matches!(op, CompareOp::Lt | CompareOp::Le) {
                            match resource.as_str() {
                                "energy" => requires.energy = Some(amount.value),
                                "latency" => requires.latency = Some(amount.value),
                                "memory" => requires.memory = Some(amount.value),
                                "carbon" => requires.carbon = Some(amount.value),
                                _ => {}
                            }
                        }
                    }
                }

                let solutions: Vec<Solution> = func
                    .solutions
                    .iter()
                    .map(|s| {
                        let mut provides = ResourceProvides::default();
                        for p in &s.provides {
                            let value = p.amount.value;
                            match p.resource.as_str() {
                                "energy" => provides.energy = Some(value),
                                "latency" => provides.latency = Some(value),
                                "memory" => provides.memory = Some(value),
                                "carbon" => provides.carbon = Some(value),
                                _ => {}
                            }
                        }
                        Solution {
                            name: s.name.clone(),
                            when_expr: s.when_clause,
                            provides,
                            body: FunctionBody::Block {
                                file_idx: 0,
                                block_idx: 0,
                            },
                        }
                    })
                    .collect();

                let value = Value::AdaptiveFunction(Rc::new(AdaptiveFunction {
                    name: func.name.clone(),
                    params: func.params.iter().map(|p| p.name.clone()).collect(),
                    solutions,
                    requires,
                    closure: self.global.clone(),
                }));
                self.global.define(func.name.clone(), value);
            }
            Item::Const(c) => {
                let value = self.eval_expr(c.value, file, &self.global.clone())?;
                self.global.define(c.name.clone(), value);
            }
            Item::TypeDef(_) => {
                // Type definitions don't create runtime values
            }
            Item::Import(_) => {
                // Imports not yet implemented
            }
        }
        Ok(())
    }

    /// Evaluate an expression.
    fn eval_expr(
        &mut self,
        expr_id: ExprId,
        file: &SourceFile,
        env: &Environment,
    ) -> RuntimeResult<Value> {
        let expr = &file.exprs[expr_id];

        match &expr.kind {
            ExprKind::Literal(lit) => Ok(self.eval_literal(lit)),

            ExprKind::Var(name) => env
                .get(name.as_str())
                .ok_or_else(|| RuntimeError::undefined(name.as_str())),

            ExprKind::Binary { op, lhs, rhs } => {
                let lhs_val = self.eval_expr(*lhs, file, env)?;
                let rhs_val = self.eval_expr(*rhs, file, env)?;
                self.eval_binary(*op, lhs_val, rhs_val)
            }

            ExprKind::Unary { op, operand } => {
                let val = self.eval_expr(*operand, file, env)?;
                self.eval_unary(*op, val)
            }

            ExprKind::Call { func, args } => {
                let callee = self.eval_expr(*func, file, env)?;
                let mut arg_values = Vec::with_capacity(args.len());
                for arg in args {
                    arg_values.push(self.eval_expr(*arg, file, env)?);
                }
                self.call_value(&callee, &arg_values, file)
            }

            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond = self.eval_expr(*condition, file, env)?;
                if cond.is_truthy() {
                    self.eval_block(then_branch, file, env)
                } else if let Some(else_block) = else_branch {
                    self.eval_block(else_block, file, env)
                } else {
                    Ok(Value::Unit)
                }
            }

            ExprKind::Block(block) => self.eval_block(block, file, env),

            ExprKind::Tuple(elems) => {
                let values: RuntimeResult<Vec<_>> = elems
                    .iter()
                    .map(|e| self.eval_expr(*e, file, env))
                    .collect();
                Ok(Value::Tuple(values?))
            }

            ExprKind::Array(elems) => {
                let values: RuntimeResult<Vec<_>> = elems
                    .iter()
                    .map(|e| self.eval_expr(*e, file, env))
                    .collect();
                Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                    values?,
                ))))
            }

            ExprKind::Index { expr, index } => {
                let arr = self.eval_expr(*expr, file, env)?;
                let idx = self.eval_expr(*index, file, env)?;

                match (&arr, idx.as_int()) {
                    (Value::Array(arr), Some(i)) => {
                        let arr = arr.borrow();
                        let i = i as usize;
                        if i < arr.len() {
                            Ok(arr[i].clone())
                        } else {
                            Err(RuntimeError::IndexOutOfBounds { index: i, len: arr.len(), span: None, hint: None })
                        }
                    }
                    (Value::Tuple(t), Some(i)) => {
                        let i = i as usize;
                        if i < t.len() {
                            Ok(t[i].clone())
                        } else {
                            Err(RuntimeError::IndexOutOfBounds { index: i, len: t.len(), span: None, hint: None })
                        }
                    }
                    _ => Err(RuntimeError::type_error("array or tuple", arr.type_name())),
                }
            }

            ExprKind::Field { expr, field } => {
                let val = self.eval_expr(*expr, file, env)?;
                match val {
                    Value::Struct { name, fields } => fields
                        .get(field)
                        .cloned()
                        .ok_or_else(|| RuntimeError::NoSuchField {
                            struct_name: name.to_string(),
                            field: field.to_string(),
                            span: None, hint: None,
                        }),
                    _ => Err(RuntimeError::type_error("struct", val.type_name())),
                }
            }

            ExprKind::Resource(amount) => Ok(Value::Resource {
                value: amount.value,
                dimension: eclexia_ast::dimension::Dimension::dimensionless(),
                unit: amount.unit.clone(),
            }),

            ExprKind::Lambda { params, body } => {
                let param_names: Vec<_> = params.iter().map(|p| p.name.clone()).collect();
                Ok(Value::Function(Rc::new(Function {
                    name: SmolStr::new("<lambda>"),
                    params: param_names,
                    body: FunctionBody::Lambda {
                        expr_id: *body,
                    },
                    closure: env.clone(),
                })))
            }

            ExprKind::Match { scrutinee, arms } => {
                let val = self.eval_expr(*scrutinee, file, env)?;
                for arm in arms {
                    if let Some(bindings) = self.match_pattern(&arm.pattern, &val) {
                        let arm_env = env.child();
                        for (name, v) in bindings {
                            arm_env.define(name, v);
                        }
                        // Check guard if present
                        if let Some(guard) = arm.guard {
                            let guard_val = self.eval_expr(guard, file, &arm_env)?;
                            if !guard_val.is_truthy() {
                                continue;
                            }
                        }
                        return self.eval_expr(arm.body, file, &arm_env);
                    }
                }
                Err(RuntimeError::custom("no matching pattern"))
            }

            ExprKind::MethodCall { receiver, method, args } => {
                let recv = self.eval_expr(*receiver, file, env)?;
                let mut arg_values = vec![recv.clone()];
                for arg in args {
                    arg_values.push(self.eval_expr(*arg, file, env)?);
                }
                // Look up method as a function
                if let Some(func) = env.get(method.as_str()) {
                    self.call_value(&func, &arg_values, file)
                } else {
                    Err(RuntimeError::undefined(method.as_str()))
                }
            }

            ExprKind::Struct { name, fields } => {
                let mut field_values = HashMap::new();
                for (field_name, field_expr) in fields {
                    let val = self.eval_expr(*field_expr, file, env)?;
                    field_values.insert(field_name.clone(), val);
                }
                Ok(Value::Struct {
                    name: name.clone(),
                    fields: field_values,
                })
            }

            ExprKind::Cast { expr, .. } => {
                // For now, just evaluate the expression (ignore the cast)
                self.eval_expr(*expr, file, env)
            }
            ExprKind::Error => Err(RuntimeError::custom("error expression")),
        }
    }

    /// Evaluate a literal.
    fn eval_literal(&self, lit: &Literal) -> Value {
        match lit {
            Literal::Int(n) => Value::Int(*n),
            Literal::Float(f) => Value::Float(*f),
            Literal::String(s) => Value::String(s.clone()),
            Literal::Char(c) => Value::Char(*c),
            Literal::Bool(b) => Value::Bool(*b),
            Literal::Unit => Value::Unit,
        }
    }

    /// Evaluate a binary operation.
    fn eval_binary(&self, op: BinaryOp, lhs: Value, rhs: Value) -> RuntimeResult<Value> {
        match op {
            BinaryOp::Add => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 + b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a + *b as f64)),
                (Value::String(a), Value::String(b)) => {
                    Ok(Value::String(SmolStr::new(format!("{}{}", a, b))))
                }
                _ => Err(RuntimeError::type_error("numeric or string", lhs.type_name())),
            },
            BinaryOp::Sub => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 - b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a - *b as f64)),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Mul => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 * b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a * *b as f64)),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Div => match (&lhs, &rhs) {
                (_, Value::Int(0)) => Err(RuntimeError::DivisionByZero { span: None, hint: None }),
                (_, Value::Float(f)) if *f == 0.0 => Err(RuntimeError::DivisionByZero { span: None, hint: None }),
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a / b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 / b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a / *b as f64)),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Rem => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a % b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::Pow => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) if *b >= 0 && *b <= 63 => {
                    // Use checked_pow to detect overflow
                    a.checked_pow(*b as u32)
                        .map(Value::Int)
                        .ok_or_else(|| RuntimeError::custom("integer overflow in power operation"))
                }
                (Value::Int(_), Value::Int(b)) if *b > 63 => {
                    Err(RuntimeError::custom("exponent too large for integer power"))
                }
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a.powf(*b))),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float((*a as f64).powf(*b))),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a.powi(*b as i32))),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Eq => Ok(Value::Bool(lhs == rhs)),
            BinaryOp::Ne => Ok(Value::Bool(lhs != rhs)),
            BinaryOp::Lt => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Bool((*a as f64) < *b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Bool(*a < (*b as f64))),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Le => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Bool((*a as f64) <= *b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Bool(*a <= (*b as f64))),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Gt => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Bool((*a as f64) > *b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Bool(*a > (*b as f64))),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::Ge => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Bool((*a as f64) >= *b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Bool(*a >= (*b as f64))),
                _ => Err(RuntimeError::type_error("numeric", lhs.type_name())),
            },
            BinaryOp::And => Ok(Value::Bool(lhs.is_truthy() && rhs.is_truthy())),
            BinaryOp::Or => Ok(Value::Bool(lhs.is_truthy() || rhs.is_truthy())),
            BinaryOp::BitAnd => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a & b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::BitOr => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a | b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::BitXor => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a ^ b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::Shl => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a << b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::Shr => match (&lhs, &rhs) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a >> b)),
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::Range => match (&lhs, &rhs) {
                (Value::Int(start), Value::Int(end)) => {
                    let values: Vec<Value> = (*start..*end).map(Value::Int).collect();
                    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(values))))
                }
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
            BinaryOp::RangeInclusive => match (&lhs, &rhs) {
                (Value::Int(start), Value::Int(end)) => {
                    let values: Vec<Value> = (*start..=*end).map(Value::Int).collect();
                    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(values))))
                }
                _ => Err(RuntimeError::type_error("integer", lhs.type_name())),
            },
        }
    }

    /// Evaluate a unary operation.
    fn eval_unary(&self, op: UnaryOp, val: Value) -> RuntimeResult<Value> {
        match op {
            UnaryOp::Neg => match val {
                Value::Int(n) => Ok(Value::Int(-n)),
                Value::Float(f) => Ok(Value::Float(-f)),
                _ => Err(RuntimeError::type_error("numeric", val.type_name())),
            },
            UnaryOp::Not => Ok(Value::Bool(!val.is_truthy())),
            UnaryOp::BitNot => match val {
                Value::Int(n) => Ok(Value::Int(!n)),
                _ => Err(RuntimeError::type_error("integer", val.type_name())),
            },
        }
    }

    /// Evaluate a block.
    fn eval_block(
        &mut self,
        block: &Block,
        file: &SourceFile,
        env: &Environment,
    ) -> RuntimeResult<Value> {
        let block_env = env.child();

        for stmt_id in &block.stmts {
            match self.eval_stmt(*stmt_id, file, &block_env) {
                Ok(_) => {}
                Err(RuntimeError::Return(v)) => return Err(RuntimeError::Return(v)),
                Err(e) => return Err(e),
            }
        }

        if let Some(expr) = block.expr {
            self.eval_expr(expr, file, &block_env)
        } else {
            Ok(Value::Unit)
        }
    }

    /// Evaluate a statement.
    fn eval_stmt(
        &mut self,
        stmt_id: StmtId,
        file: &SourceFile,
        env: &Environment,
    ) -> RuntimeResult<()> {
        let stmt = &file.stmts[stmt_id];

        match &stmt.kind {
            StmtKind::Let { name, value, .. } => {
                let val = self.eval_expr(*value, file, env)?;
                env.define(name.clone(), val);
                Ok(())
            }
            StmtKind::Expr(expr) => {
                self.eval_expr(*expr, file, env)?;
                Ok(())
            }
            StmtKind::Return(expr) => {
                let val = if let Some(e) = expr {
                    self.eval_expr(*e, file, env)?
                } else {
                    Value::Unit
                };
                Err(RuntimeError::Return(val))
            }
            StmtKind::While { condition, body } => {
                let mut iterations: u64 = 0;
                loop {
                    // Check iteration limit to prevent infinite loops
                    iterations += 1;
                    if iterations > MAX_LOOP_ITERATIONS {
                        return Err(RuntimeError::custom(format!(
                            "maximum loop iterations ({}) exceeded",
                            MAX_LOOP_ITERATIONS
                        )));
                    }

                    let cond = self.eval_expr(*condition, file, env)?;
                    if !cond.is_truthy() {
                        break;
                    }
                    match self.eval_block(body, file, env) {
                        Ok(_) => {}
                        Err(RuntimeError::Break) => break,
                        Err(RuntimeError::Continue) => continue,
                        Err(e) => return Err(e),
                    }
                }
                Ok(())
            }
            StmtKind::For { name, iter, body } => {
                let iterable = self.eval_expr(*iter, file, env)?;
                match iterable {
                    Value::Array(arr) => {
                        for val in arr.borrow().iter() {
                            let loop_env = env.child();
                            loop_env.define(name.clone(), val.clone());
                            match self.eval_block(body, file, &loop_env) {
                                Ok(_) => {}
                                Err(RuntimeError::Break) => break,
                                Err(RuntimeError::Continue) => continue,
                                Err(e) => return Err(e),
                            }
                        }
                        Ok(())
                    }
                    Value::Tuple(t) => {
                        for val in t {
                            let loop_env = env.child();
                            loop_env.define(name.clone(), val);
                            match self.eval_block(body, file, &loop_env) {
                                Ok(_) => {}
                                Err(RuntimeError::Break) => break,
                                Err(RuntimeError::Continue) => continue,
                                Err(e) => return Err(e),
                            }
                        }
                        Ok(())
                    }
                    _ => Err(RuntimeError::type_error("iterable", iterable.type_name())),
                }
            }
            StmtKind::Assign { target, value } => {
                let val = self.eval_expr(*value, file, env)?;
                if env.assign(target.as_str(), val) {
                    Ok(())
                } else {
                    Err(RuntimeError::custom(format!("undefined variable: {}", target)))
                }
            }
        }
    }

    /// Call a value as a function.
    fn call_value(
        &mut self,
        callee: &Value,
        args: &[Value],
        file: &SourceFile,
    ) -> RuntimeResult<Value> {
        // Check for recursion depth limit
        if self.call_depth >= MAX_CALL_DEPTH {
            return Err(RuntimeError::custom(format!(
                "maximum call depth of {} exceeded (possible infinite recursion)",
                MAX_CALL_DEPTH
            )));
        }
        self.call_depth += 1;
        let result = self.call_value_inner(callee, args, file);
        self.call_depth -= 1;
        result
    }

    /// Internal function call implementation.
    fn call_value_inner(
        &mut self,
        callee: &Value,
        args: &[Value],
        file: &SourceFile,
    ) -> RuntimeResult<Value> {
        match callee {
            Value::Function(func) => {
                if args.len() != func.params.len() {
                    return Err(RuntimeError::ArityMismatch {
                        expected: func.params.len(),
                        got: args.len(), hint: None,
                    });
                }

                let call_env = func.closure.child();
                for (param, arg) in func.params.iter().zip(args.iter()) {
                    call_env.define(param.clone(), arg.clone());
                }

                match &func.body {
                    FunctionBody::Lambda { expr_id } => {
                        // Lambda: evaluate the stored expression
                        match self.eval_expr(*expr_id, file, &call_env) {
                            Ok(v) => Ok(v),
                            Err(RuntimeError::Return(v)) => Ok(v),
                            Err(e) => Err(e),
                        }
                    }
                    FunctionBody::Block { .. } => {
                        // Named function: find body by name
                        for item in &file.items {
                            if let Item::Function(f) = item {
                                if f.name == func.name {
                                    // Define resource names from @requires attributes as string values
                                    for attr in &f.attributes {
                                        if attr.name.as_str() == "requires" {
                                            // Args are [resource, amount, resource, amount, ...]
                                            for chunk in attr.args.chunks(2) {
                                                if let Some(resource_name) = chunk.first() {
                                                    call_env.define(resource_name.clone(), Value::String(resource_name.clone()));
                                                }
                                            }
                                        }
                                    }
                                    // Also check constraints (for @requires: syntax)
                                    for constraint in &f.constraints {
                                        if let ConstraintKind::Resource { resource, .. } = &constraint.kind {
                                            call_env.define(resource.clone(), Value::String(resource.clone()));
                                        }
                                    }
                                    match self.eval_block(&f.body, file, &call_env) {
                                        Ok(v) => return Ok(v),
                                        Err(RuntimeError::Return(v)) => return Ok(v),
                                        Err(e) => return Err(e),
                                    }
                                }
                            }
                        }
                        Ok(Value::Unit)
                    }
                }
            }

            Value::AdaptiveFunction(func) => {
                if args.len() != func.params.len() {
                    return Err(RuntimeError::ArityMismatch {
                        expected: func.params.len(),
                        got: args.len(), hint: None,
                    });
                }

                // Create call environment with parameters bound (needed for @when evaluation)
                let call_env = func.closure.child();
                for (param, arg) in func.params.iter().zip(args.iter()) {
                    call_env.define(param.clone(), arg.clone());
                }

                // Check if any solutions have @when clauses
                let has_when = func.solutions.iter().any(|s| s.when_expr.is_some());

                if has_when {
                    // Use standard selection when @when clauses exist
                    let solution_idx = self.select_solution(&func.solutions, &func.requires, file, &call_env)?;
                    let solution = &func.solutions[solution_idx];

                    eprintln!(
                        "  [adaptive] Selected solution '{}' for {}",
                        solution.name, func.name
                    );

                    if let Some(energy) = solution.provides.energy {
                        self.energy_used += energy;
                    }
                    if let Some(carbon) = solution.provides.carbon {
                        self.carbon_used += carbon;
                    }

                    for item in &file.items {
                        if let Item::AdaptiveFunction(f) = item {
                            if f.name == func.name {
                                for (i, sol) in f.solutions.iter().enumerate() {
                                    if i == solution_idx {
                                        match self.eval_block(&sol.body, file, &call_env) {
                                            Ok(v) => return Ok(v),
                                            Err(RuntimeError::Return(v)) => return Ok(v),
                                            Err(e) => return Err(e),
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    // No @when clauses: evaluate all feasible solutions, pick the one
                    // with the maximum numeric result (economics optimization)
                    let mut best_result: Option<(usize, Value)> = None;

                    for item in &file.items {
                        if let Item::AdaptiveFunction(f) = item {
                            if f.name == func.name {
                                for (i, sol) in f.solutions.iter().enumerate() {
                                    let sol_env = call_env.child();
                                    match self.eval_block(&sol.body, file, &sol_env) {
                                        Ok(v) | Err(RuntimeError::Return(v)) => {
                                            let numeric_val = match &v {
                                                Value::Int(n) => *n as f64,
                                                Value::Float(f) => *f,
                                                _ => 0.0,
                                            };
                                            let is_better = match &best_result {
                                                None => true,
                                                Some((_, prev)) => {
                                                    let prev_val = match prev {
                                                        Value::Int(n) => *n as f64,
                                                        Value::Float(f) => *f,
                                                        _ => 0.0,
                                                    };
                                                    numeric_val > prev_val
                                                }
                                            };
                                            if is_better {
                                                best_result = Some((i, v));
                                            }
                                        }
                                        Err(_) => continue,
                                    }
                                }
                            }
                        }
                    }

                    if let Some((idx, result)) = best_result {
                        let solution = &func.solutions[idx];
                        eprintln!(
                            "  [adaptive] Selected solution '{}' for {} (by output optimization)",
                            solution.name, func.name
                        );
                        if let Some(energy) = solution.provides.energy {
                            self.energy_used += energy;
                        }
                        if let Some(carbon) = solution.provides.carbon {
                            self.carbon_used += carbon;
                        }
                        return Ok(result);
                    }
                }

                Err(RuntimeError::NoSuitableSolution {
                    name: func.name.to_string(),
                    hint: None,
                })
            }

            Value::Builtin(builtin) => (builtin.func)(args),

            _ => Err(RuntimeError::NotCallable {
                ty: callee.type_name().to_string(),
                span: None, hint: None,
            }),
        }
    }

    /// Select the best solution for an adaptive function.
    fn select_solution(
        &mut self,
        solutions: &[Solution],
        requires: &ResourceRequires,
        file: &SourceFile,
        env: &Environment,
    ) -> RuntimeResult<usize> {
        if solutions.is_empty() {
            return Err(RuntimeError::custom("no solutions available"));
        }

        // Use function's @requires constraints, falling back to global budget
        let energy_limit = requires.energy.unwrap_or(self.energy_budget);
        let latency_limit = requires.latency.unwrap_or(f64::INFINITY);
        let carbon_limit = requires.carbon.unwrap_or(self.carbon_budget);

        // Simple selection: choose the solution with minimum weighted cost
        // cost = λ_energy * energy + λ_latency * latency + λ_carbon * carbon
        let mut best_idx: Option<usize> = None;
        let mut best_cost = f64::INFINITY;

        for (i, solution) in solutions.iter().enumerate() {
            // Evaluate @when clause if present
            if let Some(when_expr) = solution.when_expr {
                match self.eval_expr(when_expr, file, env) {
                    Ok(Value::Bool(false)) => continue, // Skip this solution
                    Ok(Value::Bool(true)) => {}        // Proceed to check this solution
                    Ok(v) => {
                        return Err(RuntimeError::custom(format!(
                            "@when clause must evaluate to Bool, got {}",
                            v.type_name()
                        )));
                    }
                    Err(e) => return Err(e),
                }
            }

            let energy = solution.provides.energy.unwrap_or(0.0);
            let latency = solution.provides.latency.unwrap_or(0.0);
            let carbon = solution.provides.carbon.unwrap_or(0.0);

            // Check if solution satisfies @requires constraints
            if energy > energy_limit {
                continue;
            }
            if latency > latency_limit {
                continue;
            }
            if carbon > carbon_limit {
                continue;
            }

            let cost = self.shadow_energy * energy
                + self.shadow_latency * latency
                + self.shadow_carbon * carbon;

            if cost < best_cost {
                best_cost = cost;
                best_idx = Some(i);
            }
        }

        // Return error if no solution satisfies constraints
        best_idx.ok_or_else(|| RuntimeError::ResourceViolation {
            message: format!(
                "no solution satisfies constraints (@requires: energy < {:.1}J, latency < {:.1}ms, carbon < {:.1}gCO2e)",
                energy_limit, latency_limit, carbon_limit
            ),
            hint: Some("try relaxing the resource constraints or providing more solutions".to_string()),
        })
    }

    /// Try to match a pattern against a value, returning bindings.
    fn match_pattern(&self, pattern: &Pattern, value: &Value) -> Option<Vec<(SmolStr, Value)>> {
        match pattern {
            Pattern::Wildcard => Some(vec![]),
            Pattern::Var(name) => Some(vec![(name.clone(), value.clone())]),
            Pattern::Literal(lit) => {
                let lit_val = self.eval_literal(lit);
                if lit_val == *value {
                    Some(vec![])
                } else {
                    None
                }
            }
            Pattern::Tuple(patterns) => {
                if let Value::Tuple(values) = value {
                    if patterns.len() != values.len() {
                        return None;
                    }
                    let mut bindings = vec![];
                    for (p, v) in patterns.iter().zip(values.iter()) {
                        bindings.extend(self.match_pattern(p, v)?);
                    }
                    Some(bindings)
                } else {
                    None
                }
            }
            Pattern::Constructor { name, fields } => {
                if let Value::Struct {
                    name: struct_name,
                    fields: struct_fields,
                } = value
                {
                    if name != struct_name {
                        return None;
                    }
                    // Match positional fields (simplified)
                    let mut bindings = vec![];
                    for (i, p) in fields.iter().enumerate() {
                        let field_name = SmolStr::new(format!("_{}", i));
                        if let Some(v) = struct_fields.get(&field_name) {
                            bindings.extend(self.match_pattern(p, v)?);
                        } else {
                            return None;
                        }
                    }
                    Some(bindings)
                } else {
                    None
                }
            }
        }
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}
