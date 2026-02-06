// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime values for the Eclexia interpreter.

use eclexia_ast::dimension::Dimension;
use eclexia_ast::ExprId;
use smol_str::SmolStr;
use std::collections::{HashMap, BTreeMap};
use std::rc::Rc;
use std::cell::RefCell;

/// A runtime value in Eclexia.
#[derive(Debug, Clone)]
pub enum Value {
    /// Unit value ()
    Unit,
    /// Boolean
    Bool(bool),
    /// Integer (64-bit signed)
    Int(i64),
    /// Floating point (64-bit)
    Float(f64),
    /// String
    String(SmolStr),
    /// Character
    Char(char),
    /// Resource value with dimension
    Resource {
        value: f64,
        dimension: Dimension,
        unit: Option<SmolStr>,
    },
    /// Tuple
    Tuple(Vec<Value>),
    /// Array
    Array(Rc<RefCell<Vec<Value>>>),
    /// HashMap: key-value lookup table (keys are strings for simplicity)
    HashMap(Rc<RefCell<HashMap<SmolStr, Value>>>),
    /// SortedMap: ordered key-value map (keys are strings, ordered lexicographically)
    SortedMap(Rc<RefCell<BTreeMap<SmolStr, Value>>>),
    /// Struct instance
    Struct {
        name: SmolStr,
        fields: HashMap<SmolStr, Value>,
    },
    /// Function (closure)
    Function(Rc<Function>),
    /// Adaptive function
    AdaptiveFunction(Rc<AdaptiveFunction>),
    /// Built-in function
    Builtin(BuiltinFn),
}

/// A user-defined function.
#[derive(Debug)]
pub struct Function {
    pub name: SmolStr,
    pub params: Vec<SmolStr>,
    pub body: FunctionBody,
    pub closure: super::env::Environment,
}

/// Function body reference.
#[derive(Debug, Clone, Copy)]
pub enum FunctionBody {
    /// Reference to a block in the AST (for named functions)
    Block {
        file_idx: usize,
        block_idx: usize,
    },
    /// Reference to an expression (for lambdas)
    Lambda {
        expr_id: ExprId,
    },
}

/// An adaptive function with multiple solutions.
#[derive(Debug)]
pub struct AdaptiveFunction {
    pub name: SmolStr,
    pub params: Vec<SmolStr>,
    pub solutions: Vec<Solution>,
    pub requires: ResourceRequires,
    pub closure: super::env::Environment,
}

/// Resource requirements/constraints from @requires.
#[derive(Debug, Clone, Default)]
pub struct ResourceRequires {
    pub energy: Option<f64>,    // Max Joules
    pub latency: Option<f64>,   // Max Milliseconds
    pub memory: Option<f64>,    // Max Bytes
    pub carbon: Option<f64>,    // Max gCO2e
}

/// A solution alternative.
#[derive(Debug, Clone)]
pub struct Solution {
    pub name: SmolStr,
    pub when_expr: Option<ExprId>,
    pub provides: ResourceProvides,
    pub body: FunctionBody,
}

/// Resource provisions for a solution.
#[derive(Debug, Clone, Default)]
pub struct ResourceProvides {
    pub energy: Option<f64>,    // Joules
    pub latency: Option<f64>,   // Milliseconds
    pub memory: Option<f64>,    // Bytes
    pub carbon: Option<f64>,    // gCO2e
}

/// Built-in function type.
#[derive(Clone)]
pub struct BuiltinFn {
    pub name: &'static str,
    pub func: fn(&[Value]) -> Result<Value, super::error::RuntimeError>,
}

impl std::fmt::Debug for BuiltinFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BuiltinFn({})", self.name)
    }
}

impl Value {
    /// Check if this value is truthy.
    pub fn is_truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(n) => *n != 0,
            Value::Float(f) => *f != 0.0,
            Value::Unit => false,
            Value::String(s) => !s.is_empty(),
            Value::Array(arr) => !arr.borrow().is_empty(),
            Value::HashMap(map) => !map.borrow().is_empty(),
            Value::SortedMap(map) => !map.borrow().is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            _ => true,
        }
    }

    /// Get the type name of this value.
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Unit => "Unit",
            Value::Bool(_) => "Bool",
            Value::Int(_) => "Int",
            Value::Float(_) => "Float",
            Value::String(_) => "String",
            Value::Char(_) => "Char",
            Value::Resource { .. } => "Resource",
            Value::Tuple(_) => "Tuple",
            Value::Array(_) => "Array",
            Value::HashMap(_) => "HashMap",
            Value::SortedMap(_) => "SortedMap",
            Value::Struct { .. } => "Struct",
            Value::Function(_) => "Function",
            Value::AdaptiveFunction(_) => "AdaptiveFunction",
            Value::Builtin(_) => "Builtin",
        }
    }

    /// Try to convert to i64.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            Value::Float(f) => Some(*f as i64),
            _ => None,
        }
    }

    /// Try to convert to f64.
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Value::Int(n) => Some(*n as f64),
            Value::Float(f) => Some(*f),
            Value::Resource { value, .. } => Some(*value),
            _ => None,
        }
    }

    /// Try to convert to bool.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Char(c) => write!(f, "'{}'", c),
            Value::Resource { value, unit, .. } => {
                if let Some(u) = unit {
                    write!(f, "{}{}", value, u)
                } else {
                    write!(f, "{}", value)
                }
            }
            Value::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                if elems.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            Value::Array(arr) => {
                write!(f, "[")?;
                for (i, elem) in arr.borrow().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "]")
            }
            Value::HashMap(map) => {
                write!(f, "{{")?;
                for (i, (k, v)) in map.borrow().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "\"{}\": {}", k, v)?;
                }
                write!(f, "}}")
            }
            Value::SortedMap(map) => {
                write!(f, "SortedMap{{")?;
                for (i, (k, v)) in map.borrow().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "\"{}\": {}", k, v)?;
                }
                write!(f, "}}")
            }
            Value::Struct { name, fields } => {
                write!(f, "{} {{ ", name)?;
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, " }}")
            }
            Value::Function(func) => write!(f, "<fn {}>", func.name),
            Value::AdaptiveFunction(func) => write!(f, "<adaptive fn {}>", func.name),
            Value::Builtin(b) => write!(f, "<builtin {}>", b.name),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Float(b)) => (*a as f64) == *b,
            (Value::Float(a), Value::Int(b)) => *a == (*b as f64),
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Char(a), Value::Char(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            _ => false,
        }
    }
}
