// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Built-in functions for the Eclexia interpreter.

use crate::env::Environment;
use crate::error::{RuntimeError, RuntimeResult};
use crate::value::{BuiltinFn, Value};
use smol_str::SmolStr;

/// Register all built-in functions in the environment.
pub fn register(env: &Environment) {
    env.define(
        SmolStr::new("println"),
        Value::Builtin(BuiltinFn {
            name: "println",
            func: builtin_println,
        }),
    );

    env.define(
        SmolStr::new("print"),
        Value::Builtin(BuiltinFn {
            name: "print",
            func: builtin_print,
        }),
    );

    env.define(
        SmolStr::new("len"),
        Value::Builtin(BuiltinFn {
            name: "len",
            func: builtin_len,
        }),
    );

    env.define(
        SmolStr::new("to_string"),
        Value::Builtin(BuiltinFn {
            name: "to_string",
            func: builtin_to_string,
        }),
    );

    env.define(
        SmolStr::new("abs"),
        Value::Builtin(BuiltinFn {
            name: "abs",
            func: builtin_abs,
        }),
    );

    env.define(
        SmolStr::new("min"),
        Value::Builtin(BuiltinFn {
            name: "min",
            func: builtin_min,
        }),
    );

    env.define(
        SmolStr::new("max"),
        Value::Builtin(BuiltinFn {
            name: "max",
            func: builtin_max,
        }),
    );

    env.define(
        SmolStr::new("sqrt"),
        Value::Builtin(BuiltinFn {
            name: "sqrt",
            func: builtin_sqrt,
        }),
    );

    env.define(
        SmolStr::new("floor"),
        Value::Builtin(BuiltinFn {
            name: "floor",
            func: builtin_floor,
        }),
    );

    env.define(
        SmolStr::new("ceil"),
        Value::Builtin(BuiltinFn {
            name: "ceil",
            func: builtin_ceil,
        }),
    );

    env.define(
        SmolStr::new("range"),
        Value::Builtin(BuiltinFn {
            name: "range",
            func: builtin_range,
        }),
    );

    env.define(
        SmolStr::new("push"),
        Value::Builtin(BuiltinFn {
            name: "push",
            func: builtin_push,
        }),
    );

    env.define(
        SmolStr::new("pop"),
        Value::Builtin(BuiltinFn {
            name: "pop",
            func: builtin_pop,
        }),
    );

    // Resource-related builtins
    env.define(
        SmolStr::new("current_energy"),
        Value::Builtin(BuiltinFn {
            name: "current_energy",
            func: builtin_current_energy,
        }),
    );

    env.define(
        SmolStr::new("current_carbon"),
        Value::Builtin(BuiltinFn {
            name: "current_carbon",
            func: builtin_current_carbon,
        }),
    );

    // Condition helpers for adaptive blocks
    env.define(
        SmolStr::new("gpu_available"),
        Value::Builtin(BuiltinFn {
            name: "gpu_available",
            func: builtin_gpu_available,
        }),
    );

    env.define(
        SmolStr::new("cpu_cores"),
        Value::Builtin(BuiltinFn {
            name: "cpu_cores",
            func: builtin_cpu_cores,
        }),
    );

    // JSON support (for SustainaBot FFI!)
    env.define(
        SmolStr::new("parse_json"),
        Value::Builtin(BuiltinFn {
            name: "parse_json",
            func: builtin_parse_json,
        }),
    );

    env.define(
        SmolStr::new("to_json"),
        Value::Builtin(BuiltinFn {
            name: "to_json",
            func: builtin_to_json,
        }),
    );

    // File I/O
    env.define(
        SmolStr::new("read_file"),
        Value::Builtin(BuiltinFn {
            name: "read_file",
            func: builtin_read_file,
        }),
    );

    env.define(
        SmolStr::new("write_file"),
        Value::Builtin(BuiltinFn {
            name: "write_file",
            func: builtin_write_file,
        }),
    );

    env.define(
        SmolStr::new("file_exists"),
        Value::Builtin(BuiltinFn {
            name: "file_exists",
            func: builtin_file_exists,
        }),
    );

    // String operations
    env.define(
        SmolStr::new("str_trim"),
        Value::Builtin(BuiltinFn {
            name: "str_trim",
            func: builtin_str_trim,
        }),
    );

    env.define(
        SmolStr::new("str_split"),
        Value::Builtin(BuiltinFn {
            name: "str_split",
            func: builtin_str_split,
        }),
    );

    env.define(
        SmolStr::new("str_contains"),
        Value::Builtin(BuiltinFn {
            name: "str_contains",
            func: builtin_str_contains,
        }),
    );

    // Array operations
    env.define(
        SmolStr::new("array_map"),
        Value::Builtin(BuiltinFn {
            name: "array_map",
            func: builtin_array_map,
        }),
    );

    env.define(
        SmolStr::new("array_filter"),
        Value::Builtin(BuiltinFn {
            name: "array_filter",
            func: builtin_array_filter,
        }),
    );

    env.define(
        SmolStr::new("array_sum"),
        Value::Builtin(BuiltinFn {
            name: "array_sum",
            func: builtin_array_sum,
        }),
    );

    // More math
    env.define(
        SmolStr::new("pow"),
        Value::Builtin(BuiltinFn {
            name: "pow",
            func: builtin_pow,
        }),
    );

    env.define(
        SmolStr::new("log"),
        Value::Builtin(BuiltinFn {
            name: "log",
            func: builtin_log,
        }),
    );

    env.define(
        SmolStr::new("exp"),
        Value::Builtin(BuiltinFn {
            name: "exp",
            func: builtin_exp,
        }),
    );
}

fn builtin_println(args: &[Value]) -> RuntimeResult<Value> {
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        match arg {
            Value::String(s) => print!("{}", s),
            other => print!("{}", other),
        }
    }
    println!();
    Ok(Value::Unit)
}

fn builtin_print(args: &[Value]) -> RuntimeResult<Value> {
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        match arg {
            Value::String(s) => print!("{}", s),
            other => print!("{}", other),
        }
    }
    Ok(Value::Unit)
}

fn builtin_len(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(s) => Ok(Value::Int(s.len() as i64)),
        Value::Array(arr) => Ok(Value::Int(arr.borrow().len() as i64)),
        Value::Tuple(t) => Ok(Value::Int(t.len() as i64)),
        other => Err(RuntimeError::type_error("string, array, or tuple", other.type_name())),
    }
}

fn builtin_to_string(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    Ok(Value::String(SmolStr::new(format!("{}", args[0]))))
}

fn builtin_abs(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Int(n) => Ok(Value::Int(n.abs())),
        Value::Float(f) => Ok(Value::Float(f.abs())),
        other => Err(RuntimeError::type_error("numeric", other.type_name())),
    }
}

fn builtin_min(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1]) {
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(*a.min(b))),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a.min(*b))),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float((*a as f64).min(*b))),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a.min(*b as f64))),
        (a, _) => Err(RuntimeError::type_error("numeric", a.type_name())),
    }
}

fn builtin_max(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1]) {
        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(*a.max(b))),
        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a.max(*b))),
        (Value::Int(a), Value::Float(b)) => Ok(Value::Float((*a as f64).max(*b))),
        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a.max(*b as f64))),
        (a, _) => Err(RuntimeError::type_error("numeric", a.type_name())),
    }
}

fn builtin_sqrt(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Int(n) => Ok(Value::Float((*n as f64).sqrt())),
        Value::Float(f) => Ok(Value::Float(f.sqrt())),
        other => Err(RuntimeError::type_error("numeric", other.type_name())),
    }
}

fn builtin_floor(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Float(f) => Ok(Value::Int(f.floor() as i64)),
        Value::Int(n) => Ok(Value::Int(*n)),
        other => Err(RuntimeError::type_error("numeric", other.type_name())),
    }
}

fn builtin_ceil(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Float(f) => Ok(Value::Int(f.ceil() as i64)),
        Value::Int(n) => Ok(Value::Int(*n)),
        other => Err(RuntimeError::type_error("numeric", other.type_name())),
    }
}

/// Maximum range size to prevent memory exhaustion
const MAX_RANGE_SIZE: i64 = 1_000_000;

fn builtin_range(args: &[Value]) -> RuntimeResult<Value> {
    let (start, end) = match args.len() {
        1 => (0, args[0].as_int().ok_or_else(|| {
            RuntimeError::type_error("integer", args[0].type_name())
        })?),
        2 => {
            let s = args[0].as_int().ok_or_else(|| {
                RuntimeError::type_error("integer", args[0].type_name())
            })?;
            let e = args[1].as_int().ok_or_else(|| {
                RuntimeError::type_error("integer", args[1].type_name())
            })?;
            (s, e)
        }
        _ => {
            return Err(RuntimeError::ArityMismatch {
                expected: 2,
                got: args.len(), hint: None,
            })
        }
    };

    // Check range size limit to prevent memory exhaustion
    let size = end.saturating_sub(start);
    if size > MAX_RANGE_SIZE {
        return Err(RuntimeError::custom(format!(
            "range size {} exceeds maximum of {}",
            size, MAX_RANGE_SIZE
        )));
    }
    if size < 0 {
        // Empty range for negative size
        return Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(vec![]))));
    }

    let values: Vec<Value> = (start..end).map(Value::Int).collect();
    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        values,
    ))))
}

fn builtin_push(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            arr.borrow_mut().push(args[1].clone());
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error("array", other.type_name())),
    }
}

fn builtin_pop(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => arr
            .borrow_mut()
            .pop()
            .ok_or_else(|| RuntimeError::custom("pop from empty array")),
        other => Err(RuntimeError::type_error("array", other.type_name())),
    }
}

fn builtin_current_energy(_args: &[Value]) -> RuntimeResult<Value> {
    // In a real implementation, this would query the runtime
    Ok(Value::Resource {
        value: 0.0,
        dimension: eclexia_ast::dimension::Dimension::energy(),
        unit: Some(SmolStr::new("J")),
    })
}

fn builtin_current_carbon(_args: &[Value]) -> RuntimeResult<Value> {
    // In a real implementation, this would query the runtime
    Ok(Value::Resource {
        value: 0.0,
        dimension: eclexia_ast::dimension::Dimension::carbon(),
        unit: Some(SmolStr::new("gCO2e")),
    })
}

fn builtin_gpu_available(_args: &[Value]) -> RuntimeResult<Value> {
    // Check for GPU availability (simplified - always returns false for now)
    Ok(Value::Bool(false))
}

fn builtin_cpu_cores(_args: &[Value]) -> RuntimeResult<Value> {
    // Return number of CPU cores
    Ok(Value::Int(std::thread::available_parallelism()
        .map(|p| p.get() as i64)
        .unwrap_or(1)))
}

// ============================================================================
// JSON Support (for SustainaBot FFI)
// ============================================================================

fn builtin_parse_json(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(s) => json_to_value(s)
            .map_err(|e| RuntimeError::custom(format!("JSON parse error: {}", e))),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_to_json(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    value_to_json(&args[0])
        .map(|s| Value::String(SmolStr::new(&s)))
        .map_err(|e| RuntimeError::custom(format!("JSON serialization error: {}", e)))
}

/// Convert serde_json::Value to Eclexia Value
fn json_to_value(json_str: &str) -> Result<Value, serde_json::Error> {
    let json_val: serde_json::Value = serde_json::from_str(json_str)?;
    Ok(json_value_to_eclexia(&json_val))
}

fn json_value_to_eclexia(json: &serde_json::Value) -> Value {
    use serde_json::Value as J;
    match json {
        J::Null => Value::Unit,
        J::Bool(b) => Value::Bool(*b),
        J::Number(n) => {
            if let Some(i) = n.as_i64() {
                Value::Int(i)
            } else if let Some(f) = n.as_f64() {
                Value::Float(f)
            } else {
                Value::Float(0.0) // Fallback
            }
        }
        J::String(s) => Value::String(SmolStr::new(s)),
        J::Array(arr) => {
            let values: Vec<Value> = arr.iter().map(json_value_to_eclexia).collect();
            Value::Array(std::rc::Rc::new(std::cell::RefCell::new(values)))
        }
        J::Object(obj) => {
            // Convert to array of [key, value] pairs
            let pairs: Vec<Value> = obj
                .iter()
                .map(|(k, v)| {
                    Value::Array(std::rc::Rc::new(std::cell::RefCell::new(vec![
                        Value::String(SmolStr::new(k)),
                        json_value_to_eclexia(v),
                    ])))
                })
                .collect();
            Value::Array(std::rc::Rc::new(std::cell::RefCell::new(pairs)))
        }
    }
}

/// Convert Eclexia Value to JSON string
fn value_to_json(val: &Value) -> Result<String, String> {
    let json_val = eclexia_to_json_value(val)?;
    serde_json::to_string(&json_val).map_err(|e| e.to_string())
}

fn eclexia_to_json_value(val: &Value) -> Result<serde_json::Value, String> {
    use serde_json::Value as J;
    match val {
        Value::Unit => Ok(J::Null),
        Value::Bool(b) => Ok(J::Bool(*b)),
        Value::Int(i) => Ok(J::Number((*i).into())),
        Value::Float(f) => serde_json::Number::from_f64(*f)
            .map(J::Number)
            .ok_or_else(|| format!("Invalid float: {}", f)),
        Value::String(s) => Ok(J::String(s.to_string())),
        Value::Array(arr) => {
            let values: Result<Vec<J>, String> = arr
                .borrow()
                .iter()
                .map(eclexia_to_json_value)
                .collect();
            Ok(J::Array(values?))
        }
        Value::Resource { value, dimension, .. } => {
            // Serialize as {value: f64, dimension: string}
            Ok(serde_json::json!({
                "value": value,
                "dimension": format!("{:?}", dimension)
            }))
        }
        _ => Err(format!("Cannot convert {} to JSON", val.type_name())),
    }
}

// ============================================================================
// File I/O
// ============================================================================

fn builtin_read_file(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(path) => std::fs::read_to_string(path.as_str())
            .map(|s| Value::String(SmolStr::new(&s)))
            .map_err(|e| RuntimeError::custom(format!("Failed to read file: {}", e))),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_write_file(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1]) {
        (Value::String(path), Value::String(content)) => std::fs::write(path.as_str(), content.as_str())
            .map(|_| Value::Unit)
            .map_err(|e| RuntimeError::custom(format!("Failed to write file: {}", e))),
        (Value::String(_), other) => Err(RuntimeError::type_error("string", other.type_name())),
        (other, _) => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_file_exists(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(path) => Ok(Value::Bool(std::path::Path::new(path.as_str()).exists())),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

// ============================================================================
// String Operations
// ============================================================================

fn builtin_str_trim(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(s) => Ok(Value::String(SmolStr::new(s.trim()))),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_str_split(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1]) {
        (Value::String(s), Value::String(sep)) => {
            let parts: Vec<Value> = s
                .split(sep.as_str())
                .map(|part| Value::String(SmolStr::new(part)))
                .collect();

            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(parts))))
        }
        (Value::String(_), other) => Err(RuntimeError::type_error("string", other.type_name())),
        (other, _) => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_str_contains(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1]) {
        (Value::String(s), Value::String(needle)) => Ok(Value::Bool(s.contains(needle.as_str()))),
        (Value::String(_), other) => Err(RuntimeError::type_error("string", other.type_name())),
        (other, _) => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

// ============================================================================
// Array Operations (Higher-order functions)
// ============================================================================

fn builtin_array_map(_args: &[Value]) -> RuntimeResult<Value> {
    // TODO: Implement map with closures
    // For now, return error
    Err(RuntimeError::custom("array_map requires closure support (coming soon)"))
}

fn builtin_array_filter(_args: &[Value]) -> RuntimeResult<Value> {
    // TODO: Implement filter with closures
    Err(RuntimeError::custom("array_filter requires closure support (coming soon)"))
}

fn builtin_array_sum(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            let mut sum_int: i64 = 0;
            let mut sum_float: f64 = 0.0;
            let mut has_float = false;

            for val in arr.borrow().iter() {
                match val {
                    Value::Int(n) => {
                        if has_float {
                            sum_float += *n as f64;
                        } else {
                            sum_int += n;
                        }
                    }
                    Value::Float(f) => {
                        if !has_float {
                            sum_float = sum_int as f64;
                            has_float = true;
                        }
                        sum_float += f;
                    }
                    other => return Err(RuntimeError::type_error("number", other.type_name())),
                }
            }

            if has_float {
                Ok(Value::Float(sum_float))
            } else {
                Ok(Value::Int(sum_int))
            }
        }
        other => Err(RuntimeError::type_error("array", other.type_name())),
    }
}

// ============================================================================
// Advanced Math Functions
// ============================================================================

fn builtin_pow(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(), hint: None,
        });
    }

    let base = args[0].as_float().ok_or_else(|| {
        RuntimeError::type_error("number", args[0].type_name())
    })?;

    let exp = args[1].as_float().ok_or_else(|| {
        RuntimeError::type_error("number", args[1].type_name())
    })?;

    Ok(Value::Float(base.powf(exp)))
}

fn builtin_log(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    let n = args[0].as_float().ok_or_else(|| {
        RuntimeError::type_error("number", args[0].type_name())
    })?;

    if n <= 0.0 {
        return Err(RuntimeError::custom("log of non-positive number"));
    }

    Ok(Value::Float(n.ln()))
}

fn builtin_exp(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    let n = args[0].as_float().ok_or_else(|| {
        RuntimeError::type_error("number", args[0].type_name())
    })?;

    Ok(Value::Float(n.exp()))
}
