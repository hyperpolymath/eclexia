// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Expression and statement evaluation.

use crate::builtins;
use crate::env::Environment;
use crate::error::{RuntimeError, RuntimeResult};
use crate::value::{AdaptiveFunction, Function, FunctionBody, ResourceProvides, ResourceRequires, Solution, Value};
use eclexia_ast::*;
use eclexia_ast::TypeKind;
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
    /// Method table: type_name -> method_name -> Value::Function
    method_table: HashMap<SmolStr, HashMap<SmolStr, Value>>,
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
            method_table: HashMap::new(),
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
                // Parse @requires constraints from both sources
                let mut requires = ResourceRequires::default();

                // Source 1: constraint syntax (@requires: energy < 50J)
                for constraint in &func.constraints {
                    if let ConstraintKind::Resource { resource, op, amount } = &constraint.kind {
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

                // Source 2: attribute syntax @requires(energy: 50J)
                for attr in &func.attributes {
                    if attr.name.as_str() == "requires" {
                        for chunk in attr.args.chunks(2) {
                            if chunk.len() == 2 {
                                let num_str: String = chunk[1].chars()
                                    .take_while(|c| c.is_ascii_digit() || *c == '.')
                                    .collect();
                                if let Ok(val) = num_str.parse::<f64>() {
                                    match chunk[0].as_str() {
                                        "energy" => requires.energy = Some(val),
                                        "latency" => requires.latency = Some(val),
                                        "memory" => requires.memory = Some(val),
                                        "carbon" => requires.carbon = Some(val),
                                        _ => {}
                                    }
                                }
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
            Item::TypeDef(td) => {
                // Register enum variant constructors as functions
                if let TypeDefKind::Enum(variants) = &td.kind {
                    for variant in variants {
                        let vname = variant.name.clone();
                        match &variant.fields {
                            None => {
                                // Unit variant: register as a struct value with no fields
                                self.global.define(
                                    vname.clone(),
                                    Value::Struct {
                                        name: vname,
                                        fields: HashMap::new(),
                                    },
                                );
                            }
                            Some(field_types) => {
                                // Tuple variant: register a constructor function
                                let param_names: Vec<SmolStr> = (0..field_types.len())
                                    .map(|i| SmolStr::new(format!("_{}", i)))
                                    .collect();
                                let variant_name = vname.clone();
                                self.global.define(
                                    vname,
                                    Value::Function(Rc::new(Function {
                                        name: variant_name,
                                        params: param_names,
                                        body: FunctionBody::Block {
                                            file_idx: 0,
                                            block_idx: 0,
                                        },
                                        closure: self.global.clone(),
                                    })),
                                );
                            }
                        }
                    }
                }
                // Struct type defs don't need constructors (use ExprKind::Struct)
            }
            Item::Import(_) => {
                // Imports: for intra-file modules, resolve the path
                // Full import resolution requires a module system; skip for now
            }
            Item::TraitDecl(_) => {
                // Trait declarations: register default method bodies
                // Actual dispatch is handled via impl blocks
            }
            Item::ImplBlock(impl_block) => {
                // Register impl block methods in the method table
                let type_name = self.resolve_type_name(impl_block.self_ty, file);
                for item in &impl_block.items {
                    match item {
                        eclexia_ast::ImplItem::Method {
                            sig,
                            ..
                        } => {
                            let param_names: Vec<SmolStr> =
                                sig.params.iter().map(|p| p.name.clone()).collect();
                            let func = Value::Function(Rc::new(Function {
                                name: sig.name.clone(),
                                params: param_names,
                                body: FunctionBody::Block {
                                    file_idx: 0,
                                    block_idx: 0,
                                },
                                closure: self.global.clone(),
                            }));
                            // Store in method table
                            self.method_table
                                .entry(type_name.clone())
                                .or_default()
                                .insert(sig.name.clone(), func.clone());
                            // Also register as TypeName::method_name in global env
                            let qualified = SmolStr::new(format!("{}::{}", type_name, sig.name));
                            self.global.define(qualified, func.clone());
                        }
                        eclexia_ast::ImplItem::AssocConst {
                            name, value, ..
                        } => {
                            let val = self.eval_expr(*value, file, &self.global.clone())?;
                            let qualified = SmolStr::new(format!("{}::{}", type_name, name));
                            self.global.define(qualified, val);
                        }
                        eclexia_ast::ImplItem::AssocType { .. } => {
                            // Associated types don't create runtime values
                        }
                    }
                }
            }
            Item::ModuleDecl(module) => {
                // Module scoping: create a child environment for the module
                if let Some(ref items) = module.items {
                    let mod_env = self.global.child();
                    // Register items in the module environment
                    for item in items {
                        self.register_item_in_env(item, file, &mod_env)?;
                    }
                    // Expose module items in global env with qualified names
                    for (name, value) in mod_env.locals() {
                        let qualified = SmolStr::new(format!("{}::{}", module.name, name));
                        self.global.define(qualified, value);
                    }
                }
            }
            Item::EffectDecl(_) => {
                // Effect declarations: register effect operations as stubs
                // Full algebraic effects require continuation support
            }
            Item::StaticDecl(static_decl) => {
                // Static variable: evaluate initializer and store in global env
                let val = self.eval_expr(static_decl.value, file, &self.global.clone())?;
                self.global.define(static_decl.name.clone(), val);
            }
            Item::ExternBlock(_) => {
                // Extern blocks: foreign function stubs
                // Would need FFI integration; skip for now
            }
            Item::MacroDef(_) => {
                // Macro definitions: would need macro expansion; skip for now
            }
            Item::Error(_) => {
                // Parse error placeholder: silently skip
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

                // 1. Check method table for the receiver's type
                let type_name = self.value_type_name(&recv);
                if let Some(methods) = self.method_table.get(&type_name) {
                    if let Some(func) = methods.get(method.as_ref()) {
                        return self.call_method(&func.clone(), &arg_values, file, &recv);
                    }
                }

                // 2. Check qualified name in env (TypeName::method)
                let qualified = format!("{}::{}", type_name, method);
                if let Some(func) = env.get(&qualified) {
                    return self.call_method(&func, &arg_values, file, &recv);
                }

                // 3. Fallback: look up method as a standalone function
                if let Some(func) = env.get(method.as_str()) {
                    return self.call_value(&func, &arg_values, file);
                }

                Err(RuntimeError::custom(format!(
                    "no method '{}' found for type '{}'",
                    method, type_name
                )))
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

            ExprKind::Cast { expr, target_ty } => {
                let val = self.eval_expr(*expr, file, env)?;
                // Perform numeric conversions based on target type
                let target_type = &file.types[*target_ty];
                match &target_type.kind {
                    TypeKind::Named { name, .. } => match name.as_str() {
                        "Int" | "i64" | "i32" | "i16" | "i8" | "u64" | "u32" | "u16" | "u8"
                        | "isize" | "usize" => match &val {
                            Value::Int(_) => Ok(val),
                            Value::Float(f) => Ok(Value::Int(*f as i64)),
                            Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
                            Value::Char(c) => Ok(Value::Int(*c as i64)),
                            Value::String(s) => s
                                .parse::<i64>()
                                .map(Value::Int)
                                .map_err(|_| RuntimeError::custom(format!("cannot cast '{}' to Int", s))),
                            _ => Err(RuntimeError::type_error("numeric", val.type_name())),
                        },
                        "Float" | "f64" | "f32" => match &val {
                            Value::Float(_) => Ok(val),
                            Value::Int(n) => Ok(Value::Float(*n as f64)),
                            Value::Bool(b) => Ok(Value::Float(if *b { 1.0 } else { 0.0 })),
                            Value::String(s) => s
                                .parse::<f64>()
                                .map(Value::Float)
                                .map_err(|_| RuntimeError::custom(format!("cannot cast '{}' to Float", s))),
                            _ => Err(RuntimeError::type_error("numeric", val.type_name())),
                        },
                        "String" => Ok(Value::String(SmolStr::new(format!("{}", val)))),
                        "Bool" => Ok(Value::Bool(val.is_truthy())),
                        "Char" => match &val {
                            Value::Int(n) => char::from_u32(*n as u32)
                                .map(Value::Char)
                                .ok_or_else(|| RuntimeError::custom(format!("invalid char code: {}", n))),
                            Value::Char(_) => Ok(val),
                            _ => Err(RuntimeError::type_error("Int or Char", val.type_name())),
                        },
                        _ => Ok(val), // Unknown cast target: pass through
                    },
                    _ => Ok(val), // Non-named type: pass through
                }
            }

            ExprKind::ArrayRepeat { value, count } => {
                let val = self.eval_expr(*value, file, env)?;
                let cnt = self.eval_expr(*count, file, env)?;
                match cnt.as_int() {
                    Some(n) => {
                        let values = vec![val; n as usize];
                        Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(values))))
                    }
                    None => Err(RuntimeError::type_error("integer", cnt.type_name())),
                }
            }

            ExprKind::Try(inner) => {
                let val = self.eval_expr(*inner, file, env)?;
                match &val {
                    Value::Some(v) => Ok(*v.clone()),
                    Value::None => Err(RuntimeError::custom("try operator (?) on None value")),
                    // Handle Result types: Ok(value) unwraps, Err(e) propagates
                    Value::Struct { name, fields } if name.as_str() == "Ok" => {
                        fields
                            .get("0")
                            .cloned()
                            .ok_or_else(|| RuntimeError::custom("malformed Ok value"))
                    }
                    Value::Struct { name, fields } if name.as_str() == "Err" => {
                        let err_val = fields
                            .get("0")
                            .cloned()
                            .unwrap_or(Value::Unit);
                        Err(RuntimeError::custom(format!("try operator (?) on Err: {}", err_val)))
                    }
                    // For non-Option/Result types, pass through
                    _ => Ok(val),
                }
            }

            ExprKind::Borrow { expr, .. } => {
                // Borrow semantics not modeled in interpreter; evaluate inner expr
                self.eval_expr(*expr, file, env)
            }

            ExprKind::Deref(expr) => {
                // Deref semantics not modeled in interpreter; evaluate inner expr
                self.eval_expr(*expr, file, env)
            }

            ExprKind::AsyncBlock(block) => {
                // Simplified: evaluate async block eagerly (no actual async runtime)
                self.eval_block(block, file, env)
            }

            ExprKind::Await(expr) => {
                // Await not yet implemented; evaluate inner expression
                self.eval_expr(*expr, file, env)
            }

            ExprKind::Handle { expr, .. } => {
                // Effect handlers not yet implemented; evaluate inner expression
                self.eval_expr(*expr, file, env)
            }

            ExprKind::ReturnExpr(opt_expr) => {
                let val = if let Some(e) = opt_expr {
                    self.eval_expr(*e, file, env)?
                } else {
                    Value::Unit
                };
                Err(RuntimeError::Return(val))
            }

            ExprKind::BreakExpr { .. } => {
                // Break as expression
                Err(RuntimeError::Break)
            }

            ExprKind::ContinueExpr { .. } => {
                // Continue as expression
                Err(RuntimeError::Continue)
            }

            ExprKind::PathExpr(segments) => {
                // Try to look up the full path as a single name (e.g., Foo::bar)
                let full_name = segments.join("::");
                env.get(&full_name)
                    .or_else(|| {
                        // Fallback: try the last segment as a simple variable
                        segments.last().and_then(|s| env.get(s.as_str()))
                    })
                    .ok_or_else(|| RuntimeError::undefined(&full_name))
            }

            ExprKind::Error => Err(RuntimeError::custom("error expression")),

            // Concurrency expressions — not yet supported in interpreter
            ExprKind::Spawn(_) => Err(RuntimeError::custom("spawn not yet supported in interpreter")),
            ExprKind::Channel { .. } => Err(RuntimeError::custom("channels not yet supported in interpreter")),
            ExprKind::Send { .. } => Err(RuntimeError::custom("send not yet supported in interpreter")),
            ExprKind::Recv(_) => Err(RuntimeError::custom("recv not yet supported in interpreter")),
            ExprKind::Select { .. } => Err(RuntimeError::custom("select not yet supported in interpreter")),
            ExprKind::YieldExpr(_) => Err(RuntimeError::custom("yield not yet supported in interpreter")),
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
            StmtKind::Let { pattern, value, .. } => {
                let val = self.eval_expr(*value, file, env)?;
                self.bind_pattern(pattern, &val, env);
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
            StmtKind::For { pattern, iter, body } => {
                let iterable = self.eval_expr(*iter, file, env)?;
                match iterable {
                    Value::Array(arr) => {
                        for val in arr.borrow().iter() {
                            let loop_env = env.child();
                            self.bind_pattern(pattern, val, &loop_env);
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
                            self.bind_pattern(pattern, &val, &loop_env);
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
                // target is now an ExprId; look up the expression to get the name
                let target_expr = &file.exprs[*target];
                match &target_expr.kind {
                    ExprKind::Var(name) => {
                        if env.assign(name.as_str(), val) {
                            Ok(())
                        } else {
                            Err(RuntimeError::custom(format!("undefined variable: {}", name)))
                        }
                    }
                    ExprKind::Field { expr, field } => {
                        let base = self.eval_expr(*expr, file, env)?;
                        match base {
                            Value::Struct { name, mut fields } => {
                                fields.insert(field.clone(), val);
                                // Re-assign the whole struct back
                                // This is a simplification; proper mutation needs ref semantics
                                let base_expr = &file.exprs[*expr];
                                if let ExprKind::Var(var_name) = &base_expr.kind {
                                    env.assign(var_name.as_str(), Value::Struct { name, fields });
                                }
                                Ok(())
                            }
                            _ => Err(RuntimeError::type_error("struct", base.type_name())),
                        }
                    }
                    ExprKind::Index { expr, index } => {
                        let base = self.eval_expr(*expr, file, env)?;
                        let idx = self.eval_expr(*index, file, env)?;
                        match (&base, idx.as_int()) {
                            (Value::Array(arr), Some(i)) => {
                                let mut arr = arr.borrow_mut();
                                let i = i as usize;
                                if i < arr.len() {
                                    arr[i] = val;
                                    Ok(())
                                } else {
                                    Err(RuntimeError::IndexOutOfBounds { index: i, len: arr.len(), span: None, hint: None })
                                }
                            }
                            _ => Err(RuntimeError::type_error("array", base.type_name())),
                        }
                    }
                    _ => {
                        Err(RuntimeError::custom("unsupported assignment target".to_string()))
                    }
                }
            }
            StmtKind::Loop { body, .. } => {
                let mut iterations: u64 = 0;
                loop {
                    iterations += 1;
                    if iterations > MAX_LOOP_ITERATIONS {
                        return Err(RuntimeError::custom(format!(
                            "maximum loop iterations ({}) exceeded",
                            MAX_LOOP_ITERATIONS
                        )));
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
            StmtKind::Break { .. } => {
                Err(RuntimeError::Break)
            }
            StmtKind::Continue { .. } => {
                Err(RuntimeError::Continue)
            }
            StmtKind::Error => {
                // Parse error placeholder: evaluate to unit (no-op)
                Ok(())
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
                                    // Parse and enforce @requires constraints.
                                    // Constraints come from two sources:
                                    //   1. f.constraints (parsed from `@requires: energy < 50J`)
                                    //   2. f.attributes  (parsed from `@requires(energy: 50J)`)
                                    let mut fn_energy_limit: Option<f64> = None;

                                    // Source 1: constraint syntax
                                    for constraint in &f.constraints {
                                        if let ConstraintKind::Resource { resource, op, amount } = &constraint.kind {
                                            call_env.define(resource.clone(), Value::String(resource.clone()));
                                            if matches!(op, CompareOp::Lt | CompareOp::Le) {
                                                match resource.as_str() {
                                                    "energy" => fn_energy_limit = Some(amount.value),
                                                    _ => {}
                                                }
                                            }
                                        }
                                    }

                                    // Source 2: attribute syntax @requires(energy: 50J)
                                    for attr in &f.attributes {
                                        if attr.name.as_str() == "requires" {
                                            for chunk in attr.args.chunks(2) {
                                                if chunk.len() == 2 {
                                                    let resource_name = &chunk[0];
                                                    let amount_str = &chunk[1];
                                                    call_env.define(resource_name.clone(), Value::String(resource_name.clone()));
                                                    if resource_name.as_str() == "energy" {
                                                        // Parse amount: "0J", "15J", "25J" etc.
                                                        let num_str: String = amount_str.chars()
                                                            .take_while(|c| c.is_ascii_digit() || *c == '.')
                                                            .collect();
                                                        if let Ok(val) = num_str.parse::<f64>() {
                                                            fn_energy_limit = Some(val);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    // Enforce @requires energy budget.
                                    // A function with @requires(energy: N) declares a
                                    // ceiling of N joules.  Calling it adds N to the
                                    // caller's tracked consumption.  If the body's
                                    // sub-calls exceed N, we reject.
                                    if let Some(limit) = fn_energy_limit {
                                        // Zero budget means impossible to execute
                                        if limit == 0.0 {
                                            return Err(RuntimeError::ResourceViolation {
                                                message: format!(
                                                    "function '{}' has @requires(energy: 0J) — zero budget cannot be satisfied",
                                                    f.name
                                                ),
                                                hint: Some("increase the energy budget or remove the @requires constraint".to_string()),
                                            });
                                        }
                                        // Add declared cost to caller's accounting
                                        self.energy_used += limit;
                                        // Check caller's budget immediately
                                        if self.energy_used > self.energy_budget {
                                            return Err(RuntimeError::ResourceViolation {
                                                message: format!(
                                                    "calling '{}' would use {:.1}J total, exceeding budget of {:.1}J",
                                                    f.name, self.energy_used, self.energy_budget
                                                ),
                                                hint: Some("reduce resource consumption or increase the @requires budget".to_string()),
                                            });
                                        }
                                    }
                                    // Save and set callee's own budget scope
                                    let saved_energy = self.energy_used;
                                    let saved_budget = self.energy_budget;
                                    if let Some(limit) = fn_energy_limit {
                                        self.energy_used = 0.0;
                                        self.energy_budget = limit;
                                    }
                                    let result = match self.eval_block(&f.body, file, &call_env) {
                                        Ok(v) => Ok(v),
                                        Err(RuntimeError::Return(v)) => Ok(v),
                                        Err(e) => Err(e),
                                    };
                                    // Restore caller's budget scope
                                    if fn_energy_limit.is_some() {
                                        self.energy_used = saved_energy;
                                        self.energy_budget = saved_budget;
                                    }
                                    return result;
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
                    // with the maximum numeric result (economics optimization).
                    // Solutions are first filtered by @requires feasibility.
                    let energy_limit = func.requires.energy.unwrap_or(self.energy_budget);
                    let latency_limit = func.requires.latency.unwrap_or(f64::INFINITY);
                    let carbon_limit = func.requires.carbon.unwrap_or(self.carbon_budget);

                    let mut best_result: Option<(usize, Value)> = None;

                    for item in &file.items {
                        if let Item::AdaptiveFunction(f) = item {
                            if f.name == func.name {
                                for (i, sol) in f.solutions.iter().enumerate() {
                                    // Check feasibility: solution @provides must fit within @requires
                                    let sol_provides = &func.solutions[i].provides;
                                    if sol_provides.energy.unwrap_or(0.0) > energy_limit {
                                        continue;
                                    }
                                    if sol_provides.latency.unwrap_or(0.0) > latency_limit {
                                        continue;
                                    }
                                    if sol_provides.carbon.unwrap_or(0.0) > carbon_limit {
                                        continue;
                                    }

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
            Pattern::Struct { name, fields, rest } => {
                if let Value::Struct {
                    name: struct_name,
                    fields: struct_fields,
                } = value
                {
                    if name != struct_name {
                        return None;
                    }
                    let mut bindings = vec![];
                    for fp in fields {
                        if let Some(v) = struct_fields.get(&fp.name) {
                            if let Some(ref pat) = fp.pattern {
                                bindings.extend(self.match_pattern(pat, v)?);
                            } else {
                                // Shorthand: field name is also the binding
                                bindings.push((fp.name.clone(), v.clone()));
                            }
                        } else if !rest {
                            return None;
                        }
                    }
                    Some(bindings)
                } else {
                    None
                }
            }
            Pattern::Slice(patterns) => {
                if let Value::Array(arr) = value {
                    let arr = arr.borrow();
                    if patterns.len() != arr.len() {
                        return None;
                    }
                    let mut bindings = vec![];
                    for (p, v) in patterns.iter().zip(arr.iter()) {
                        bindings.extend(self.match_pattern(p, v)?);
                    }
                    Some(bindings)
                } else {
                    None
                }
            }
            Pattern::Or(patterns) => {
                // Try each alternative; return bindings from the first match
                for p in patterns {
                    if let Some(bindings) = self.match_pattern(p, value) {
                        return Some(bindings);
                    }
                }
                None
            }
            Pattern::Range { start, end, inclusive } => {
                // Match numeric ranges
                let val_num = match value {
                    Value::Int(n) => Some(*n as f64),
                    Value::Float(f) => Some(*f),
                    _ => None,
                };
                if let Some(v) = val_num {
                    let start_ok = match start {
                        Some(pat) => {
                            let lit_val = match pat.as_ref() {
                                Pattern::Literal(lit) => Some(self.eval_literal(lit)),
                                _ => None,
                            };
                            match lit_val.and_then(|lv| lv.as_float()) {
                                Some(s) => v >= s,
                                None => false,
                            }
                        }
                        None => true,
                    };
                    let end_ok = match end {
                        Some(pat) => {
                            let lit_val = match pat.as_ref() {
                                Pattern::Literal(lit) => Some(self.eval_literal(lit)),
                                _ => None,
                            };
                            match lit_val.and_then(|lv| lv.as_float()) {
                                Some(e) => if *inclusive { v <= e } else { v < e },
                                None => false,
                            }
                        }
                        None => true,
                    };
                    if start_ok && end_ok { Some(vec![]) } else { None }
                } else {
                    None
                }
            }
            Pattern::Rest => {
                // Rest pattern (..) only meaningful inside slice/struct patterns
                Some(vec![])
            }
            Pattern::Binding { name, pattern } => {
                // name @ pattern: bind the whole value and also match sub-pattern
                if let Some(mut bindings) = self.match_pattern(pattern, value) {
                    bindings.push((name.clone(), value.clone()));
                    Some(bindings)
                } else {
                    None
                }
            }
            Pattern::Reference { pattern, .. } => {
                // Reference patterns not modeled in interpreter; match inner pattern
                self.match_pattern(pattern, value)
            }
        }
    }

    /// Bind a pattern to a value, defining variables in the environment.
    fn bind_pattern(&self, pattern: &Pattern, value: &Value, env: &Environment) {
        match pattern {
            Pattern::Var(name) => {
                env.define(name.clone(), value.clone());
            }
            Pattern::Wildcard => {
                // No binding needed
            }
            Pattern::Tuple(patterns) => {
                if let Value::Tuple(values) = value {
                    for (pat, val) in patterns.iter().zip(values.iter()) {
                        self.bind_pattern(pat, val, env);
                    }
                }
            }
            Pattern::Slice(patterns) => {
                if let Value::Array(arr) = value {
                    let arr = arr.borrow();
                    for (pat, val) in patterns.iter().zip(arr.iter()) {
                        self.bind_pattern(pat, val, env);
                    }
                }
            }
            Pattern::Struct { name: _, fields, .. } => {
                if let Value::Struct { fields: struct_fields, .. } = value {
                    for fp in fields {
                        if let Some(val) = struct_fields.get(&fp.name) {
                            if let Some(ref pat) = fp.pattern {
                                self.bind_pattern(pat, val, env);
                            } else {
                                // Shorthand: field name is also the binding
                                env.define(fp.name.clone(), val.clone());
                            }
                        }
                    }
                }
            }
            Pattern::Constructor { name: _, fields } => {
                // Treat constructor fields as positional bindings
                if let Value::Tuple(values) = value {
                    for (pat, val) in fields.iter().zip(values.iter()) {
                        self.bind_pattern(pat, val, env);
                    }
                }
            }
            Pattern::Binding { name, pattern } => {
                // Bind the whole value and also destructure
                env.define(name.clone(), value.clone());
                self.bind_pattern(pattern, value, env);
            }
            Pattern::Reference { pattern, .. } => {
                // References not modeled; destructure inner
                self.bind_pattern(pattern, value, env);
            }
            Pattern::Or(patterns) => {
                // Try each alternative; bind from the first match
                for pat in patterns {
                    if self.match_pattern(pat, value).is_some() {
                        self.bind_pattern(pat, value, env);
                        break;
                    }
                }
            }
            Pattern::Literal(_) | Pattern::Range { .. } | Pattern::Rest => {
                // Literals, ranges, and rest don't bind variables
            }
        }
    }

    /// Resolve a TypeId to a type name string (for method table lookups).
    fn resolve_type_name(&self, type_id: TypeId, file: &SourceFile) -> SmolStr {
        let ty = &file.types[type_id];
        match &ty.kind {
            TypeKind::Named { name, .. } => name.clone(),
            _ => SmolStr::new("<unknown>"),
        }
    }

    /// Get the runtime type name of a Value (for method dispatch).
    fn value_type_name(&self, val: &Value) -> SmolStr {
        match val {
            Value::Struct { name, .. } => name.clone(),
            Value::Array(_) => SmolStr::new("Array"),
            Value::HashMap(_) => SmolStr::new("HashMap"),
            Value::SortedMap(_) => SmolStr::new("SortedMap"),
            Value::String(_) => SmolStr::new("String"),
            Value::Int(_) => SmolStr::new("Int"),
            Value::Float(_) => SmolStr::new("Float"),
            Value::Bool(_) => SmolStr::new("Bool"),
            Value::Char(_) => SmolStr::new("Char"),
            Value::Tuple(_) => SmolStr::new("Tuple"),
            Value::Resource { .. } => SmolStr::new("Resource"),
            Value::Some(_) | Value::None => SmolStr::new("Option"),
            Value::Function(_) => SmolStr::new("Function"),
            Value::AdaptiveFunction(_) => SmolStr::new("AdaptiveFunction"),
            Value::Builtin(_) => SmolStr::new("Builtin"),
            Value::Unit => SmolStr::new("Unit"),
        }
    }

    /// Register an item in a specific environment (for module scoping).
    fn register_item_in_env(
        &mut self,
        item: &Item,
        file: &SourceFile,
        env: &Environment,
    ) -> RuntimeResult<()> {
        match item {
            Item::Function(func) => {
                let value = Value::Function(Rc::new(Function {
                    name: func.name.clone(),
                    params: func.params.iter().map(|p| p.name.clone()).collect(),
                    body: FunctionBody::Block {
                        file_idx: 0,
                        block_idx: 0,
                    },
                    closure: env.clone(),
                }));
                env.define(func.name.clone(), value);
            }
            Item::Const(c) => {
                let value = self.eval_expr(c.value, file, &env.clone())?;
                env.define(c.name.clone(), value);
            }
            Item::StaticDecl(s) => {
                let value = self.eval_expr(s.value, file, &env.clone())?;
                env.define(s.name.clone(), value);
            }
            _ => {
                // Other items in module scope: delegate to register_item
                // which puts them in global; acceptable for now
            }
        }
        Ok(())
    }

    /// Call a method on a value, finding the correct body in the file's items.
    fn call_method(
        &mut self,
        callee: &Value,
        args: &[Value],
        file: &SourceFile,
        receiver: &Value,
    ) -> RuntimeResult<Value> {
        if self.call_depth >= MAX_CALL_DEPTH {
            return Err(RuntimeError::custom(format!(
                "maximum call depth of {} exceeded (possible infinite recursion)",
                MAX_CALL_DEPTH
            )));
        }
        self.call_depth += 1;

        let result = match callee {
            Value::Function(func) => {
                let call_env = func.closure.child();
                // Bind 'self' parameter if first param matches
                let mut param_iter = func.params.iter();
                let mut arg_iter = args.iter();

                if let Some(first_param) = param_iter.next() {
                    if first_param.as_str() == "self" || first_param.as_str() == "&self" {
                        call_env.define(SmolStr::new("self"), receiver.clone());
                        arg_iter.next(); // skip receiver in args
                    } else {
                        if let Some(arg) = arg_iter.next() {
                            call_env.define(first_param.clone(), arg.clone());
                        }
                    }
                }

                for (param, arg) in param_iter.zip(arg_iter) {
                    call_env.define(param.clone(), arg.clone());
                }

                // Find the method body in impl blocks
                let type_name = self.value_type_name(receiver);
                for item in &file.items {
                    if let Item::ImplBlock(impl_block) = item {
                        let impl_type = self.resolve_type_name(impl_block.self_ty, file);
                        if impl_type == type_name {
                            for impl_item in &impl_block.items {
                                if let eclexia_ast::ImplItem::Method {
                                    sig, body, ..
                                } = impl_item
                                {
                                    if sig.name == func.name {
                                        let r = self.eval_block(body, file, &call_env);
                                        self.call_depth -= 1;
                                        return match r {
                                            Ok(v) => Ok(v),
                                            Err(RuntimeError::Return(v)) => Ok(v),
                                            Err(e) => Err(e),
                                        };
                                    }
                                }
                            }
                        }
                    }
                }

                // Fallback: try as regular function call
                self.call_depth -= 1;
                return self.call_value(callee, args, file);
            }
            _ => self.call_value_inner(callee, args, file),
        };

        self.call_depth -= 1;
        result
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}
