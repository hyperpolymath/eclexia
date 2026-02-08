// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Built-in functions for the Eclexia interpreter.

use crate::env::Environment;
use crate::error::{RuntimeError, RuntimeResult};
use crate::value::{BuiltinFn, Value};
use smol_str::SmolStr;
use std::collections::{HashMap, BTreeMap};

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

    env.define(
        SmolStr::new("str_to_lowercase"),
        Value::Builtin(BuiltinFn {
            name: "str_to_lowercase",
            func: builtin_str_to_lowercase,
        }),
    );

    env.define(
        SmolStr::new("str_to_uppercase"),
        Value::Builtin(BuiltinFn {
            name: "str_to_uppercase",
            func: builtin_str_to_uppercase,
        }),
    );

    env.define(
        SmolStr::new("str_replace"),
        Value::Builtin(BuiltinFn {
            name: "str_replace",
            func: builtin_str_replace,
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

    // Time operations
    env.define(
        SmolStr::new("time_now_ms"),
        Value::Builtin(BuiltinFn {
            name: "time_now_ms",
            func: builtin_time_now_ms,
        }),
    );

    env.define(
        SmolStr::new("time_unix_timestamp"),
        Value::Builtin(BuiltinFn {
            name: "time_unix_timestamp",
            func: builtin_time_unix_timestamp,
        }),
    );

    env.define(
        SmolStr::new("time_sleep_ms"),
        Value::Builtin(BuiltinFn {
            name: "time_sleep_ms",
            func: builtin_time_sleep_ms,
        }),
    );

    env.define(
        SmolStr::new("time_hour"),
        Value::Builtin(BuiltinFn {
            name: "time_hour",
            func: builtin_time_hour,
        }),
    );

    env.define(
        SmolStr::new("time_day_of_week"),
        Value::Builtin(BuiltinFn {
            name: "time_day_of_week",
            func: builtin_time_day_of_week,
        }),
    );

    env.define(
        SmolStr::new("time_to_iso8601"),
        Value::Builtin(BuiltinFn {
            name: "time_to_iso8601",
            func: builtin_time_to_iso8601,
        }),
    );

    env.define(
        SmolStr::new("time_from_iso8601"),
        Value::Builtin(BuiltinFn {
            name: "time_from_iso8601",
            func: builtin_time_from_iso8601,
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

    // ========================================================================
    // Collections: HashMap
    // ========================================================================

    env.define(
        SmolStr::new("hashmap_new"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_new",
            func: builtin_hashmap_new,
        }),
    );

    env.define(
        SmolStr::new("hashmap_insert"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_insert",
            func: builtin_hashmap_insert,
        }),
    );

    env.define(
        SmolStr::new("hashmap_get"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_get",
            func: builtin_hashmap_get,
        }),
    );

    env.define(
        SmolStr::new("hashmap_remove"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_remove",
            func: builtin_hashmap_remove,
        }),
    );

    env.define(
        SmolStr::new("hashmap_contains"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_contains",
            func: builtin_hashmap_contains,
        }),
    );

    env.define(
        SmolStr::new("hashmap_len"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_len",
            func: builtin_hashmap_len,
        }),
    );

    env.define(
        SmolStr::new("hashmap_keys"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_keys",
            func: builtin_hashmap_keys,
        }),
    );

    env.define(
        SmolStr::new("hashmap_values"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_values",
            func: builtin_hashmap_values,
        }),
    );

    env.define(
        SmolStr::new("hashmap_entries"),
        Value::Builtin(BuiltinFn {
            name: "hashmap_entries",
            func: builtin_hashmap_entries,
        }),
    );

    // ========================================================================
    // Collections: SortedMap (BTreeMap-backed, ordered by key)
    // ========================================================================

    env.define(
        SmolStr::new("sortedmap_new"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_new",
            func: builtin_sortedmap_new,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_insert"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_insert",
            func: builtin_sortedmap_insert,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_get"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_get",
            func: builtin_sortedmap_get,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_remove"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_remove",
            func: builtin_sortedmap_remove,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_len"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_len",
            func: builtin_sortedmap_len,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_keys"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_keys",
            func: builtin_sortedmap_keys,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_min_key"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_min_key",
            func: builtin_sortedmap_min_key,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_max_key"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_max_key",
            func: builtin_sortedmap_max_key,
        }),
    );

    env.define(
        SmolStr::new("sortedmap_range"),
        Value::Builtin(BuiltinFn {
            name: "sortedmap_range",
            func: builtin_sortedmap_range,
        }),
    );

    // ========================================================================
    // Collections: Queue (FIFO) and PriorityQueue
    // ========================================================================

    env.define(
        SmolStr::new("queue_new"),
        Value::Builtin(BuiltinFn {
            name: "queue_new",
            func: builtin_queue_new,
        }),
    );

    env.define(
        SmolStr::new("queue_enqueue"),
        Value::Builtin(BuiltinFn {
            name: "queue_enqueue",
            func: builtin_queue_enqueue,
        }),
    );

    env.define(
        SmolStr::new("queue_dequeue"),
        Value::Builtin(BuiltinFn {
            name: "queue_dequeue",
            func: builtin_queue_dequeue,
        }),
    );

    env.define(
        SmolStr::new("queue_peek"),
        Value::Builtin(BuiltinFn {
            name: "queue_peek",
            func: builtin_queue_peek,
        }),
    );

    env.define(
        SmolStr::new("queue_len"),
        Value::Builtin(BuiltinFn {
            name: "queue_len",
            func: builtin_queue_len,
        }),
    );

    env.define(
        SmolStr::new("queue_is_empty"),
        Value::Builtin(BuiltinFn {
            name: "queue_is_empty",
            func: builtin_queue_is_empty,
        }),
    );

    env.define(
        SmolStr::new("priority_queue_new"),
        Value::Builtin(BuiltinFn {
            name: "priority_queue_new",
            func: builtin_priority_queue_new,
        }),
    );

    env.define(
        SmolStr::new("priority_queue_push"),
        Value::Builtin(BuiltinFn {
            name: "priority_queue_push",
            func: builtin_priority_queue_push,
        }),
    );

    env.define(
        SmolStr::new("priority_queue_pop"),
        Value::Builtin(BuiltinFn {
            name: "priority_queue_pop",
            func: builtin_priority_queue_pop,
        }),
    );

    env.define(
        SmolStr::new("priority_queue_peek"),
        Value::Builtin(BuiltinFn {
            name: "priority_queue_peek",
            func: builtin_priority_queue_peek,
        }),
    );

    env.define(
        SmolStr::new("priority_queue_len"),
        Value::Builtin(BuiltinFn {
            name: "priority_queue_len",
            func: builtin_priority_queue_len,
        }),
    );

    // ========================================================================
    // Collections: Set operations (on arrays)
    // ========================================================================

    env.define(
        SmolStr::new("set_union"),
        Value::Builtin(BuiltinFn {
            name: "set_union",
            func: builtin_set_union,
        }),
    );

    env.define(
        SmolStr::new("set_intersection"),
        Value::Builtin(BuiltinFn {
            name: "set_intersection",
            func: builtin_set_intersection,
        }),
    );

    env.define(
        SmolStr::new("set_difference"),
        Value::Builtin(BuiltinFn {
            name: "set_difference",
            func: builtin_set_difference,
        }),
    );

    env.define(
        SmolStr::new("set_symmetric_difference"),
        Value::Builtin(BuiltinFn {
            name: "set_symmetric_difference",
            func: builtin_set_symmetric_difference,
        }),
    );

    env.define(
        SmolStr::new("set_is_subset"),
        Value::Builtin(BuiltinFn {
            name: "set_is_subset",
            func: builtin_set_is_subset,
        }),
    );

    env.define(
        SmolStr::new("set_from_array"),
        Value::Builtin(BuiltinFn {
            name: "set_from_array",
            func: builtin_set_from_array,
        }),
    );

    // Standard library essentials
    env.define(
        SmolStr::new("assert"),
        Value::Builtin(BuiltinFn {
            name: "assert",
            func: builtin_assert,
        }),
    );

    env.define(
        SmolStr::new("panic"),
        Value::Builtin(BuiltinFn {
            name: "panic",
            func: builtin_panic,
        }),
    );

    // Option type constructors
    env.define(
        SmolStr::new("Some"),
        Value::Builtin(BuiltinFn {
            name: "Some",
            func: builtin_some,
        }),
    );

    env.define(SmolStr::new("None"), Value::None);

    // Result type constructors
    env.define(
        SmolStr::new("Ok"),
        Value::Builtin(BuiltinFn {
            name: "Ok",
            func: builtin_ok,
        }),
    );

    env.define(
        SmolStr::new("Err"),
        Value::Builtin(BuiltinFn {
            name: "Err",
            func: builtin_err,
        }),
    );

    // Economics-specific functions
    env.define(
        SmolStr::new("shadow_price"),
        Value::Builtin(BuiltinFn {
            name: "shadow_price",
            func: builtin_shadow_price,
        }),
    );

    // Option/Result helper methods (as standalone functions)
    env.define(
        SmolStr::new("is_some"),
        Value::Builtin(BuiltinFn {
            name: "is_some",
            func: builtin_is_some,
        }),
    );

    env.define(
        SmolStr::new("is_none"),
        Value::Builtin(BuiltinFn {
            name: "is_none",
            func: builtin_is_none,
        }),
    );

    env.define(
        SmolStr::new("is_ok"),
        Value::Builtin(BuiltinFn {
            name: "is_ok",
            func: builtin_is_ok,
        }),
    );

    env.define(
        SmolStr::new("is_err"),
        Value::Builtin(BuiltinFn {
            name: "is_err",
            func: builtin_is_err,
        }),
    );

    env.define(
        SmolStr::new("unwrap"),
        Value::Builtin(BuiltinFn {
            name: "unwrap",
            func: builtin_unwrap,
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
        Value::HashMap(map) => Ok(Value::Int(map.borrow().len() as i64)),
        Value::SortedMap(map) => Ok(Value::Int(map.borrow().len() as i64)),
        other => Err(RuntimeError::type_error("string, array, tuple, HashMap, or SortedMap", other.type_name())),
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
        Value::HashMap(map) => {
            let mut obj = serde_json::Map::new();
            for (k, v) in map.borrow().iter() {
                obj.insert(k.to_string(), eclexia_to_json_value(v)?);
            }
            Ok(J::Object(obj))
        }
        Value::SortedMap(map) => {
            let mut obj = serde_json::Map::new();
            for (k, v) in map.borrow().iter() {
                obj.insert(k.to_string(), eclexia_to_json_value(v)?);
            }
            Ok(J::Object(obj))
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

fn builtin_str_to_lowercase(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(s) => Ok(Value::String(SmolStr::new(&s.to_lowercase()))),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_str_to_uppercase(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(s) => Ok(Value::String(SmolStr::new(&s.to_uppercase()))),
        other => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

fn builtin_str_replace(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 3 {
        return Err(RuntimeError::ArityMismatch {
            expected: 3,
            got: args.len(), hint: None,
        });
    }

    match (&args[0], &args[1], &args[2]) {
        (Value::String(s), Value::String(pattern), Value::String(replacement)) => {
            let result = s.replace(pattern.as_str(), replacement.as_str());
            Ok(Value::String(SmolStr::new(&result)))
        }
        (Value::String(_), Value::String(_), other) => {
            Err(RuntimeError::type_error("string", other.type_name()))
        }
        (Value::String(_), other, _) => Err(RuntimeError::type_error("string", other.type_name())),
        (other, _, _) => Err(RuntimeError::type_error("string", other.type_name())),
    }
}

// ============================================================================
// Time Operations
// ============================================================================

fn builtin_time_now_ms(_args: &[Value]) -> RuntimeResult<Value> {
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| RuntimeError::custom(&format!("Time error: {}", e)))?;

    Ok(Value::Int(now.as_millis() as i64))
}

fn builtin_time_unix_timestamp(_args: &[Value]) -> RuntimeResult<Value> {
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| RuntimeError::custom(&format!("Time error: {}", e)))?;

    Ok(Value::Int(now.as_secs() as i64))
}

fn builtin_time_sleep_ms(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Int(millis) => {
            if *millis < 0 {
                return Err(RuntimeError::custom("sleep duration must be non-negative"));
            }
            std::thread::sleep(std::time::Duration::from_millis(*millis as u64));
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error("integer", other.type_name())),
    }
}

fn builtin_time_hour(_args: &[Value]) -> RuntimeResult<Value> {
    // Simple implementation using local time
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| RuntimeError::custom(&format!("Time error: {}", e)))?;

    // Simplified: hour from UTC (full impl would need timezone handling)
    let secs = now.as_secs();
    let hour = (secs / 3600) % 24;

    Ok(Value::Int(hour as i64))
}

fn builtin_time_day_of_week(_args: &[Value]) -> RuntimeResult<Value> {
    // Simple implementation: days since Unix epoch (Thursday)
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| RuntimeError::custom(&format!("Time error: {}", e)))?;

    let days = now.as_secs() / 86400;
    // Unix epoch (1970-01-01) was a Thursday (4), so add 4 and mod 7
    let day_of_week = (days + 4) % 7;

    Ok(Value::Int(day_of_week as i64))
}

fn builtin_time_to_iso8601(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::Int(timestamp) => {
            // Simple ISO 8601 formatting (YYYY-MM-DDTHH:MM:SSZ)
            // Note: This is simplified; full impl would use chrono or similar
            let secs = *timestamp as u64;
            let days = secs / 86400;
            let year = 1970 + (days / 365);  // Approximate

            // Simplified format
            let iso = format!("{:04}-01-01T00:00:00Z", year);
            Ok(Value::String(SmolStr::new(&iso)))
        }
        other => Err(RuntimeError::type_error("integer", other.type_name())),
    }
}

fn builtin_time_from_iso8601(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(), hint: None,
        });
    }

    match &args[0] {
        Value::String(iso_str) => {
            // Simplified parsing - just extract year and convert to timestamp
            // Note: This is simplified; full impl would use chrono or similar
            if let Some(year_str) = iso_str.split('-').next() {
                if let Ok(year) = year_str.parse::<i64>() {
                    // Approximate timestamp (seconds since 1970)
                    let timestamp = (year - 1970) * 365 * 86400;
                    return Ok(Value::Int(timestamp));
                }
            }
            Err(RuntimeError::custom("Invalid ISO 8601 format"))
        }
        other => Err(RuntimeError::type_error("string", other.type_name())),
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

// ============================================================================
// Collections: HashMap builtins
// ============================================================================

/// Extract a string key from a Value, converting integers and floats to strings.
fn value_to_key(val: &Value) -> RuntimeResult<SmolStr> {
    match val {
        Value::String(s) => Ok(s.clone()),
        Value::Int(n) => Ok(SmolStr::new(n.to_string())),
        Value::Float(f) => Ok(SmolStr::new(f.to_string())),
        Value::Bool(b) => Ok(SmolStr::new(b.to_string())),
        other => Err(RuntimeError::type_error(
            "string, int, float, or bool (for key)",
            other.type_name(),
        )),
    }
}

fn builtin_hashmap_new(_args: &[Value]) -> RuntimeResult<Value> {
    Ok(Value::HashMap(std::rc::Rc::new(std::cell::RefCell::new(
        HashMap::new(),
    ))))
}

fn builtin_hashmap_insert(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 3 {
        return Err(RuntimeError::ArityMismatch {
            expected: 3,
            got: args.len(),
            hint: Some("usage: hashmap_insert(map, key, value)".to_string()),
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let key = value_to_key(&args[1])?;
            map.borrow_mut().insert(key, args[2].clone());
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_get(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: hashmap_get(map, key)".to_string()),
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let key = value_to_key(&args[1])?;
            match map.borrow().get(&key) {
                Some(val) => Ok(val.clone()),
                None => Ok(Value::Unit), // None equivalent
            }
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_remove(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: hashmap_remove(map, key)".to_string()),
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let key = value_to_key(&args[1])?;
            match map.borrow_mut().remove(&key) {
                Some(val) => Ok(val),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_contains(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: hashmap_contains(map, key)".to_string()),
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let key = value_to_key(&args[1])?;
            Ok(Value::Bool(map.borrow().contains_key(&key)))
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_len(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::HashMap(map) => Ok(Value::Int(map.borrow().len() as i64)),
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_keys(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let keys: Vec<Value> = map
                .borrow()
                .keys()
                .map(|k| Value::String(k.clone()))
                .collect();
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                keys,
            ))))
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_values(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let values: Vec<Value> = map.borrow().values().cloned().collect();
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                values,
            ))))
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

fn builtin_hashmap_entries(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::HashMap(map) => {
            let entries: Vec<Value> = map
                .borrow()
                .iter()
                .map(|(k, v)| Value::Tuple(vec![Value::String(k.clone()), v.clone()]))
                .collect();
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                entries,
            ))))
        }
        other => Err(RuntimeError::type_error("HashMap", other.type_name())),
    }
}

// ============================================================================
// Collections: SortedMap builtins (BTreeMap-backed, for ordered economic data)
// ============================================================================

fn builtin_sortedmap_new(_args: &[Value]) -> RuntimeResult<Value> {
    Ok(Value::SortedMap(std::rc::Rc::new(
        std::cell::RefCell::new(BTreeMap::new()),
    )))
}

fn builtin_sortedmap_insert(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 3 {
        return Err(RuntimeError::ArityMismatch {
            expected: 3,
            got: args.len(),
            hint: Some("usage: sortedmap_insert(map, key, value)".to_string()),
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let key = value_to_key(&args[1])?;
            map.borrow_mut().insert(key, args[2].clone());
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_get(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: sortedmap_get(map, key)".to_string()),
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let key = value_to_key(&args[1])?;
            match map.borrow().get(&key) {
                Some(val) => Ok(val.clone()),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_remove(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: sortedmap_remove(map, key)".to_string()),
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let key = value_to_key(&args[1])?;
            match map.borrow_mut().remove(&key) {
                Some(val) => Ok(val),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_len(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => Ok(Value::Int(map.borrow().len() as i64)),
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_keys(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let keys: Vec<Value> = map
                .borrow()
                .keys()
                .map(|k| Value::String(k.clone()))
                .collect();
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                keys,
            ))))
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_min_key(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let borrowed = map.borrow();
            match borrowed.iter().next() {
                Some((k, v)) => Ok(Value::Tuple(vec![Value::String(k.clone()), v.clone()])),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_max_key(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let borrowed = map.borrow();
            match borrowed.iter().next_back() {
                Some((k, v)) => Ok(Value::Tuple(vec![Value::String(k.clone()), v.clone()])),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

fn builtin_sortedmap_range(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 3 {
        return Err(RuntimeError::ArityMismatch {
            expected: 3,
            got: args.len(),
            hint: Some("usage: sortedmap_range(map, from_key, to_key)".to_string()),
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let from = value_to_key(&args[1])?;
            let to = value_to_key(&args[2])?;
            let borrowed = map.borrow();
            let entries: Vec<Value> = borrowed
                .range(from..=to)
                .map(|(k, v)| Value::Tuple(vec![Value::String(k.clone()), v.clone()]))
                .collect();
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                entries,
            ))))
        }
        other => Err(RuntimeError::type_error("SortedMap", other.type_name())),
    }
}

// ============================================================================
// Collections: Queue (FIFO, backed by Array)
// ============================================================================

fn builtin_queue_new(_args: &[Value]) -> RuntimeResult<Value> {
    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        Vec::new(),
    ))))
}

fn builtin_queue_enqueue(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: queue_enqueue(queue, value)".to_string()),
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            arr.borrow_mut().push(args[1].clone());
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error("Queue (Array)", other.type_name())),
    }
}

fn builtin_queue_dequeue(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            let mut borrowed = arr.borrow_mut();
            if borrowed.is_empty() {
                Err(RuntimeError::custom("dequeue from empty queue"))
            } else {
                Ok(borrowed.remove(0))
            }
        }
        other => Err(RuntimeError::type_error("Queue (Array)", other.type_name())),
    }
}

fn builtin_queue_peek(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            let borrowed = arr.borrow();
            match borrowed.first() {
                Some(val) => Ok(val.clone()),
                None => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error("Queue (Array)", other.type_name())),
    }
}

fn builtin_queue_len(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => Ok(Value::Int(arr.borrow().len() as i64)),
        other => Err(RuntimeError::type_error("Queue (Array)", other.type_name())),
    }
}

fn builtin_queue_is_empty(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::Array(arr) => Ok(Value::Bool(arr.borrow().is_empty())),
        other => Err(RuntimeError::type_error("Queue (Array)", other.type_name())),
    }
}

// ============================================================================
// Collections: PriorityQueue (min-heap using SortedMap with numeric keys)
//
// Stored as a SortedMap where keys are priority scores (as strings for BTreeMap
// ordering). Lower numeric values have higher priority (min-heap).
// Each priority maps to an array of values with that priority.
// ============================================================================

fn builtin_priority_queue_new(_args: &[Value]) -> RuntimeResult<Value> {
    Ok(Value::SortedMap(std::rc::Rc::new(
        std::cell::RefCell::new(BTreeMap::new()),
    )))
}

fn builtin_priority_queue_push(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 3 {
        return Err(RuntimeError::ArityMismatch {
            expected: 3,
            got: args.len(),
            hint: Some("usage: priority_queue_push(pq, priority, value)".to_string()),
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let priority = match &args[1] {
                Value::Int(n) => format!("{:020}", n), // Zero-pad for correct string sort
                Value::Float(f) => format!("{:020.10}", f),
                other => {
                    return Err(RuntimeError::type_error("number (priority)", other.type_name()))
                }
            };
            let key = SmolStr::new(&priority);
            let mut borrowed = map.borrow_mut();
            let entry = borrowed.entry(key).or_insert_with(|| {
                Value::Array(std::rc::Rc::new(std::cell::RefCell::new(Vec::new())))
            });
            match entry {
                Value::Array(arr) => {
                    arr.borrow_mut().push(args[2].clone());
                }
                _ => return Err(RuntimeError::custom("internal error: priority queue entry is not an array")),
            }
            Ok(Value::Unit)
        }
        other => Err(RuntimeError::type_error(
            "PriorityQueue (SortedMap)",
            other.type_name(),
        )),
    }
}

fn builtin_priority_queue_pop(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let mut borrowed = map.borrow_mut();
            let first_key = borrowed.keys().next().cloned();
            match first_key {
                Some(key) => {
                    let result = if let Some(Value::Array(arr)) = borrowed.get(&key) {
                        let mut arr_borrowed = arr.borrow_mut();
                        if arr_borrowed.is_empty() {
                            None
                        } else {
                            Some(arr_borrowed.remove(0))
                        }
                    } else {
                        None
                    };

                    // Clean up empty priority buckets
                    if let Some(Value::Array(arr)) = borrowed.get(&key) {
                        if arr.borrow().is_empty() {
                            borrowed.remove(&key);
                        }
                    }

                    match result {
                        Some(val) => Ok(val),
                        None => Err(RuntimeError::custom("pop from empty priority queue")),
                    }
                }
                None => Err(RuntimeError::custom("pop from empty priority queue")),
            }
        }
        other => Err(RuntimeError::type_error(
            "PriorityQueue (SortedMap)",
            other.type_name(),
        )),
    }
}

fn builtin_priority_queue_peek(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let borrowed = map.borrow();
            match borrowed.iter().next() {
                Some((_key, Value::Array(arr))) => {
                    let arr_borrowed = arr.borrow();
                    match arr_borrowed.first() {
                        Some(val) => Ok(val.clone()),
                        None => Ok(Value::Unit),
                    }
                }
                _ => Ok(Value::Unit),
            }
        }
        other => Err(RuntimeError::type_error(
            "PriorityQueue (SortedMap)",
            other.type_name(),
        )),
    }
}

fn builtin_priority_queue_len(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: None,
        });
    }

    match &args[0] {
        Value::SortedMap(map) => {
            let borrowed = map.borrow();
            let total: usize = borrowed
                .values()
                .map(|v| match v {
                    Value::Array(arr) => arr.borrow().len(),
                    _ => 1,
                })
                .sum();
            Ok(Value::Int(total as i64))
        }
        other => Err(RuntimeError::type_error(
            "PriorityQueue (SortedMap)",
            other.type_name(),
        )),
    }
}

// ============================================================================
// Collections: Set operations (operate on HashSet backed by arrays for now)
//
// Sets are represented as arrays with unique elements. These functions perform
// standard set algebra operations, essential for economic modeling (market
// participants, policy groups, resource categories).
// ============================================================================

/// Helper: extract unique string representations from an array Value
fn array_to_string_set(val: &Value) -> RuntimeResult<std::collections::HashSet<String>> {
    match val {
        Value::Array(arr) => {
            let borrowed = arr.borrow();
            let mut set = std::collections::HashSet::new();
            for v in borrowed.iter() {
                set.insert(format!("{}", v));
            }
            Ok(set)
        }
        other => Err(RuntimeError::type_error("Array (Set)", other.type_name())),
    }
}

/// Helper: build array from set, preserving the original values from source
fn values_in_set(
    source: &Value,
    set: &std::collections::HashSet<String>,
) -> RuntimeResult<Vec<Value>> {
    match source {
        Value::Array(arr) => {
            let borrowed = arr.borrow();
            let mut result = Vec::new();
            let mut seen = std::collections::HashSet::new();
            for v in borrowed.iter() {
                let repr = format!("{}", v);
                if set.contains(&repr) && seen.insert(repr) {
                    result.push(v.clone());
                }
            }
            Ok(result)
        }
        other => Err(RuntimeError::type_error("Array (Set)", other.type_name())),
    }
}

fn builtin_set_union(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: set_union(set_a, set_b)".to_string()),
        });
    }

    let set_a = array_to_string_set(&args[0])?;
    let set_b = array_to_string_set(&args[1])?;
    let union: std::collections::HashSet<String> = set_a.union(&set_b).cloned().collect();

    // Collect values from both arrays, deduplicating
    let mut result = values_in_set(&args[0], &union)?;
    let a_reprs: std::collections::HashSet<String> = result.iter().map(|v| format!("{}", v)).collect();
    // Add items from B that aren't already present
    if let Value::Array(arr_b) = &args[1] {
        for v in arr_b.borrow().iter() {
            let repr = format!("{}", v);
            if union.contains(&repr) && !a_reprs.contains(&repr) {
                result.push(v.clone());
            }
        }
    }

    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        result,
    ))))
}

fn builtin_set_intersection(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: set_intersection(set_a, set_b)".to_string()),
        });
    }

    let set_a = array_to_string_set(&args[0])?;
    let set_b = array_to_string_set(&args[1])?;
    let intersection: std::collections::HashSet<String> =
        set_a.intersection(&set_b).cloned().collect();
    let result = values_in_set(&args[0], &intersection)?;

    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        result,
    ))))
}

fn builtin_set_difference(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: set_difference(set_a, set_b) returns A - B".to_string()),
        });
    }

    let set_a = array_to_string_set(&args[0])?;
    let set_b = array_to_string_set(&args[1])?;
    let diff: std::collections::HashSet<String> = set_a.difference(&set_b).cloned().collect();
    let result = values_in_set(&args[0], &diff)?;

    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        result,
    ))))
}

fn builtin_set_symmetric_difference(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some(
                "usage: set_symmetric_difference(set_a, set_b) returns (A-B) union (B-A)"
                    .to_string(),
            ),
        });
    }

    let set_a = array_to_string_set(&args[0])?;
    let set_b = array_to_string_set(&args[1])?;
    let sym_diff: std::collections::HashSet<String> =
        set_a.symmetric_difference(&set_b).cloned().collect();

    let mut result = values_in_set(&args[0], &sym_diff)?;
    let a_reprs: std::collections::HashSet<String> = result.iter().map(|v| format!("{}", v)).collect();
    if let Value::Array(arr_b) = &args[1] {
        for v in arr_b.borrow().iter() {
            let repr = format!("{}", v);
            if sym_diff.contains(&repr) && !a_reprs.contains(&repr) {
                result.push(v.clone());
            }
        }
    }

    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        result,
    ))))
}

fn builtin_set_is_subset(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
            hint: Some("usage: set_is_subset(subset, superset)".to_string()),
        });
    }

    let set_a = array_to_string_set(&args[0])?;
    let set_b = array_to_string_set(&args[1])?;
    Ok(Value::Bool(set_a.is_subset(&set_b)))
}

fn builtin_set_from_array(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
            hint: Some("usage: set_from_array(arr) - deduplicate array".to_string()),
        });
    }

    match &args[0] {
        Value::Array(arr) => {
            let borrowed = arr.borrow();
            let mut seen = std::collections::HashSet::new();
            let mut result = Vec::new();
            for v in borrowed.iter() {
                let repr = format!("{}", v);
                if seen.insert(repr) {
                    result.push(v.clone());
                }
            }
            Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
                result,
            ))))
        }
        other => Err(RuntimeError::type_error("Array", other.type_name())),
    }
}

// ============================================================================
// Standard Library Essentials
// ============================================================================

/// Assert that a condition is true, panic if false.
/// Usage: assert(condition, message)
fn builtin_assert(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() < 1 {
        return Err(RuntimeError::custom("assert requires at least 1 argument (condition)"));
    }

    let condition = match &args[0] {
        Value::Bool(b) => *b,
        other => return Err(RuntimeError::type_error("Bool", other.type_name())),
    };

    if !condition {
        let message = if args.len() >= 2 {
            match &args[1] {
                Value::String(s) => s.to_string(),
                other => format!("Assertion failed: {:?}", other),
            }
        } else {
            "Assertion failed".to_string()
        };
        return Err(RuntimeError::custom(message));
    }

    Ok(Value::Unit)
}

/// Panic with a message and halt execution.
/// Usage: panic(message)
fn builtin_panic(args: &[Value]) -> RuntimeResult<Value> {
    let message = if args.is_empty() {
        "panic called".to_string()
    } else {
        match &args[0] {
            Value::String(s) => s.to_string(),
            other => format!("{:?}", other),
        }
    };

    Err(RuntimeError::custom(format!("panic: {}", message)))
}

/// Construct a Some variant of Option<T>.
/// Usage: Some(value)
fn builtin_some(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("Some requires exactly 1 argument"));
    }
    Ok(Value::Some(Box::new(args[0].clone())))
}

/// Construct a None variant of Option<T>.
/// Usage: None()
#[allow(dead_code)]
fn builtin_none(args: &[Value]) -> RuntimeResult<Value> {
    if !args.is_empty() {
        return Err(RuntimeError::custom("None takes no arguments"));
    }
    Ok(Value::None)
}

/// Construct an Ok variant of Result<T, E>.
/// Usage: Ok(value)
fn builtin_ok(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("Ok requires exactly 1 argument"));
    }

    let mut fields = HashMap::new();
    fields.insert(SmolStr::new("0"), args[0].clone());

    Ok(Value::Struct {
        name: SmolStr::new("Ok"),
        fields,
    })
}

/// Construct an Err variant of Result<T, E>.
/// Usage: Err(error)
fn builtin_err(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("Err requires exactly 1 argument"));
    }

    let mut fields = HashMap::new();
    fields.insert(SmolStr::new("0"), args[0].clone());

    Ok(Value::Struct {
        name: SmolStr::new("Err"),
        fields,
    })
}

/// Query the shadow price for a specific resource.
/// Usage: shadow_price(resource_name)
/// Returns the current shadow price (marginal value) for the resource.
fn builtin_shadow_price(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("shadow_price requires exactly 1 argument (resource name)"));
    }

    let resource_name = match &args[0] {
        Value::String(s) => s.as_str(),
        other => return Err(RuntimeError::type_error("String", other.type_name())),
    };

    // For now, return fixed shadow prices based on resource type
    // In a full implementation, this would query the runtime's optimization state
    let price = match resource_name {
        "energy" => 1.0,      // $1 per Joule
        "time" => 0.1,        // $0.10 per millisecond
        "carbon" => 50.0,     // $50 per gCO2e
        "memory" => 0.001,    // $0.001 per byte
        "latency" => 0.1,     // $0.10 per ms
        _ => 1.0,             // Default shadow price
    };

    Ok(Value::Float(price))
}

/// Check if an Option value is Some.
/// Usage: is_some(option_value)
fn builtin_is_some(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("is_some requires exactly 1 argument"));
    }
    Ok(Value::Bool(matches!(args[0], Value::Some(_))))
}

/// Check if an Option value is None.
/// Usage: is_none(option_value)
fn builtin_is_none(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("is_none requires exactly 1 argument"));
    }
    Ok(Value::Bool(matches!(args[0], Value::None)))
}

/// Check if a Result value is Ok.
/// Usage: is_ok(result_value)
fn builtin_is_ok(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("is_ok requires exactly 1 argument"));
    }

    match &args[0] {
        Value::Struct { name, .. } if name.as_str() == "Ok" => Ok(Value::Bool(true)),
        Value::Struct { name, .. } if name.as_str() == "Err" => Ok(Value::Bool(false)),
        other => Err(RuntimeError::type_error("Result", other.type_name())),
    }
}

/// Check if a Result value is Err.
/// Usage: is_err(result_value)
fn builtin_is_err(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("is_err requires exactly 1 argument"));
    }

    match &args[0] {
        Value::Struct { name, .. } if name.as_str() == "Err" => Ok(Value::Bool(true)),
        Value::Struct { name, .. } if name.as_str() == "Ok" => Ok(Value::Bool(false)),
        other => Err(RuntimeError::type_error("Result", other.type_name())),
    }
}

fn builtin_unwrap(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::custom("unwrap requires exactly 1 argument"));
    }
    match &args[0] {
        Value::Some(v) => Ok(*v.clone()),
        Value::None => Err(RuntimeError::custom("called unwrap on None value")),
        other => Err(RuntimeError::type_error("Option", other.type_name())),
    }
}

// ============================================================================
// Tests for collection builtins
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;

    fn make_array(vals: Vec<Value>) -> Value {
        Value::Array(std::rc::Rc::new(std::cell::RefCell::new(vals)))
    }

    // -- HashMap tests --

    #[test]
    fn test_hashmap_new_is_empty() {
        let map = builtin_hashmap_new(&[]).unwrap();
        assert!(matches!(map, Value::HashMap(_)));

        let len = builtin_hashmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(0));
    }

    #[test]
    fn test_hashmap_insert_and_get() {
        let map = builtin_hashmap_new(&[]).unwrap();

        // Insert ("GDP", 21.0)
        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("GDP")),
            Value::Float(21.0),
        ])
        .unwrap();

        // Get
        let val = builtin_hashmap_get(&[map.clone(), Value::String(SmolStr::new("GDP"))]).unwrap();
        assert_eq!(val, Value::Float(21.0));

        // Len should be 1
        let len = builtin_hashmap_len(&[map.clone()]).unwrap();
        assert_eq!(len, Value::Int(1));

        // Contains
        let has = builtin_hashmap_contains(&[map.clone(), Value::String(SmolStr::new("GDP"))])
            .unwrap();
        assert_eq!(has, Value::Bool(true));

        let no = builtin_hashmap_contains(&[map.clone(), Value::String(SmolStr::new("CPI"))])
            .unwrap();
        assert_eq!(no, Value::Bool(false));
    }

    #[test]
    fn test_hashmap_overwrite() {
        let map = builtin_hashmap_new(&[]).unwrap();

        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("rate")),
            Value::Float(5.25),
        ])
        .unwrap();

        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("rate")),
            Value::Float(5.50),
        ])
        .unwrap();

        let val = builtin_hashmap_get(&[map.clone(), Value::String(SmolStr::new("rate"))]).unwrap();
        assert_eq!(val, Value::Float(5.50));

        // Len should still be 1 (overwrite, not new entry)
        let len = builtin_hashmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(1));
    }

    #[test]
    fn test_hashmap_remove() {
        let map = builtin_hashmap_new(&[]).unwrap();

        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("x")),
            Value::Int(42),
        ])
        .unwrap();

        let removed = builtin_hashmap_remove(&[map.clone(), Value::String(SmolStr::new("x"))])
            .unwrap();
        assert_eq!(removed, Value::Int(42));

        let len = builtin_hashmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(0));
    }

    #[test]
    fn test_hashmap_keys_and_values() {
        let map = builtin_hashmap_new(&[]).unwrap();

        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("a")),
            Value::Int(1),
        ])
        .unwrap();
        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("b")),
            Value::Int(2),
        ])
        .unwrap();

        let keys = builtin_hashmap_keys(&[map.clone()]).unwrap();
        if let Value::Array(arr) = keys {
            assert_eq!(arr.borrow().len(), 2);
        } else {
            panic!("Expected array of keys");
        }

        let values = builtin_hashmap_values(&[map.clone()]).unwrap();
        if let Value::Array(arr) = values {
            assert_eq!(arr.borrow().len(), 2);
        } else {
            panic!("Expected array of values");
        }

        let entries = builtin_hashmap_entries(&[map]).unwrap();
        if let Value::Array(arr) = entries {
            assert_eq!(arr.borrow().len(), 2);
        } else {
            panic!("Expected array of entries");
        }
    }

    #[test]
    fn test_hashmap_integer_keys() {
        let map = builtin_hashmap_new(&[]).unwrap();

        builtin_hashmap_insert(&[map.clone(), Value::Int(2024), Value::Float(3.2)]).unwrap();

        let val = builtin_hashmap_get(&[map, Value::Int(2024)]).unwrap();
        assert_eq!(val, Value::Float(3.2));
    }

    // -- SortedMap tests --

    #[test]
    fn test_sortedmap_new_is_empty() {
        let map = builtin_sortedmap_new(&[]).unwrap();
        assert!(matches!(map, Value::SortedMap(_)));

        let len = builtin_sortedmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(0));
    }

    #[test]
    fn test_sortedmap_insert_and_get() {
        let map = builtin_sortedmap_new(&[]).unwrap();

        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("2024-Q1")),
            Value::Float(3.2),
        ])
        .unwrap();

        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("2024-Q2")),
            Value::Float(3.5),
        ])
        .unwrap();

        let val = builtin_sortedmap_get(&[map.clone(), Value::String(SmolStr::new("2024-Q1"))])
            .unwrap();
        assert_eq!(val, Value::Float(3.2));

        let len = builtin_sortedmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(2));
    }

    #[test]
    fn test_sortedmap_keys_are_sorted() {
        let map = builtin_sortedmap_new(&[]).unwrap();

        // Insert out of order
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("c")),
            Value::Int(3),
        ])
        .unwrap();
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("a")),
            Value::Int(1),
        ])
        .unwrap();
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("b")),
            Value::Int(2),
        ])
        .unwrap();

        let keys = builtin_sortedmap_keys(&[map]).unwrap();
        if let Value::Array(arr) = keys {
            let borrowed = arr.borrow();
            assert_eq!(borrowed.len(), 3);
            assert_eq!(borrowed[0], Value::String(SmolStr::new("a")));
            assert_eq!(borrowed[1], Value::String(SmolStr::new("b")));
            assert_eq!(borrowed[2], Value::String(SmolStr::new("c")));
        } else {
            panic!("Expected array of keys");
        }
    }

    #[test]
    fn test_sortedmap_min_max() {
        let map = builtin_sortedmap_new(&[]).unwrap();

        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("2023")),
            Value::Float(1.5),
        ])
        .unwrap();
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("2025")),
            Value::Float(3.5),
        ])
        .unwrap();
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("2024")),
            Value::Float(2.5),
        ])
        .unwrap();

        let min = builtin_sortedmap_min_key(&[map.clone()]).unwrap();
        if let Value::Tuple(elems) = min {
            assert_eq!(elems[0], Value::String(SmolStr::new("2023")));
            assert_eq!(elems[1], Value::Float(1.5));
        } else {
            panic!("Expected tuple (key, value)");
        }

        let max = builtin_sortedmap_max_key(&[map]).unwrap();
        if let Value::Tuple(elems) = max {
            assert_eq!(elems[0], Value::String(SmolStr::new("2025")));
            assert_eq!(elems[1], Value::Float(3.5));
        } else {
            panic!("Expected tuple (key, value)");
        }
    }

    #[test]
    fn test_sortedmap_range_query() {
        let map = builtin_sortedmap_new(&[]).unwrap();

        for year in ["2020", "2021", "2022", "2023", "2024", "2025"] {
            builtin_sortedmap_insert(&[
                map.clone(),
                Value::String(SmolStr::new(year)),
                Value::Int(year.parse::<i64>().unwrap()),
            ])
            .unwrap();
        }

        let range = builtin_sortedmap_range(&[
            map,
            Value::String(SmolStr::new("2022")),
            Value::String(SmolStr::new("2024")),
        ])
        .unwrap();

        if let Value::Array(arr) = range {
            let borrowed = arr.borrow();
            assert_eq!(borrowed.len(), 3); // 2022, 2023, 2024
        } else {
            panic!("Expected array of entries");
        }
    }

    #[test]
    fn test_sortedmap_remove() {
        let map = builtin_sortedmap_new(&[]).unwrap();

        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("key")),
            Value::Int(99),
        ])
        .unwrap();

        let removed =
            builtin_sortedmap_remove(&[map.clone(), Value::String(SmolStr::new("key"))]).unwrap();
        assert_eq!(removed, Value::Int(99));

        let len = builtin_sortedmap_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(0));
    }

    // -- Queue tests --

    #[test]
    fn test_queue_fifo() {
        let queue = builtin_queue_new(&[]).unwrap();

        builtin_queue_enqueue(&[queue.clone(), Value::Int(1)]).unwrap();
        builtin_queue_enqueue(&[queue.clone(), Value::Int(2)]).unwrap();
        builtin_queue_enqueue(&[queue.clone(), Value::Int(3)]).unwrap();

        let len = builtin_queue_len(&[queue.clone()]).unwrap();
        assert_eq!(len, Value::Int(3));

        // FIFO: first in, first out
        let first = builtin_queue_dequeue(&[queue.clone()]).unwrap();
        assert_eq!(first, Value::Int(1));

        let second = builtin_queue_dequeue(&[queue.clone()]).unwrap();
        assert_eq!(second, Value::Int(2));

        let third = builtin_queue_dequeue(&[queue.clone()]).unwrap();
        assert_eq!(third, Value::Int(3));

        let is_empty = builtin_queue_is_empty(&[queue]).unwrap();
        assert_eq!(is_empty, Value::Bool(true));
    }

    #[test]
    fn test_queue_peek() {
        let queue = builtin_queue_new(&[]).unwrap();

        builtin_queue_enqueue(&[queue.clone(), Value::String(SmolStr::new("event_a"))]).unwrap();

        let peeked = builtin_queue_peek(&[queue.clone()]).unwrap();
        assert_eq!(peeked, Value::String(SmolStr::new("event_a")));

        // Peek should not remove
        let len = builtin_queue_len(&[queue]).unwrap();
        assert_eq!(len, Value::Int(1));
    }

    #[test]
    fn test_queue_dequeue_empty_errors() {
        let queue = builtin_queue_new(&[]).unwrap();
        let result = builtin_queue_dequeue(&[queue]);
        assert!(result.is_err());
    }

    // -- PriorityQueue tests --

    #[test]
    fn test_priority_queue_min_first() {
        let pq = builtin_priority_queue_new(&[]).unwrap();

        // Push with different priorities (lower = higher urgency)
        builtin_priority_queue_push(&[
            pq.clone(),
            Value::Int(5),
            Value::String(SmolStr::new("low")),
        ])
        .unwrap();
        builtin_priority_queue_push(&[
            pq.clone(),
            Value::Int(1),
            Value::String(SmolStr::new("high")),
        ])
        .unwrap();
        builtin_priority_queue_push(&[
            pq.clone(),
            Value::Int(3),
            Value::String(SmolStr::new("medium")),
        ])
        .unwrap();

        let len = builtin_priority_queue_len(&[pq.clone()]).unwrap();
        assert_eq!(len, Value::Int(3));

        // Should pop in priority order: high(1), medium(3), low(5)
        let first = builtin_priority_queue_pop(&[pq.clone()]).unwrap();
        assert_eq!(first, Value::String(SmolStr::new("high")));

        let second = builtin_priority_queue_pop(&[pq.clone()]).unwrap();
        assert_eq!(second, Value::String(SmolStr::new("medium")));

        let third = builtin_priority_queue_pop(&[pq]).unwrap();
        assert_eq!(third, Value::String(SmolStr::new("low")));
    }

    #[test]
    fn test_priority_queue_peek() {
        let pq = builtin_priority_queue_new(&[]).unwrap();

        builtin_priority_queue_push(&[pq.clone(), Value::Int(10), Value::Int(42)]).unwrap();

        let peeked = builtin_priority_queue_peek(&[pq.clone()]).unwrap();
        assert_eq!(peeked, Value::Int(42));

        // Peek should not remove
        let len = builtin_priority_queue_len(&[pq]).unwrap();
        assert_eq!(len, Value::Int(1));
    }

    #[test]
    fn test_priority_queue_pop_empty_errors() {
        let pq = builtin_priority_queue_new(&[]).unwrap();
        let result = builtin_priority_queue_pop(&[pq]);
        assert!(result.is_err());
    }

    // -- Set operations tests --

    #[test]
    fn test_set_union() {
        let a = make_array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let b = make_array(vec![Value::Int(3), Value::Int(4), Value::Int(5)]);

        let result = builtin_set_union(&[a, b]).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.borrow().len(), 5); // {1,2,3,4,5}
        } else {
            panic!("Expected array");
        }
    }

    #[test]
    fn test_set_intersection() {
        let a = make_array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let b = make_array(vec![Value::Int(2), Value::Int(3), Value::Int(4)]);

        let result = builtin_set_intersection(&[a, b]).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.borrow().len(), 2); // {2, 3}
        } else {
            panic!("Expected array");
        }
    }

    #[test]
    fn test_set_difference() {
        let a = make_array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let b = make_array(vec![Value::Int(2), Value::Int(4)]);

        let result = builtin_set_difference(&[a, b]).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.borrow().len(), 2); // {1, 3}
        } else {
            panic!("Expected array");
        }
    }

    #[test]
    fn test_set_symmetric_difference() {
        let a = make_array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let b = make_array(vec![Value::Int(2), Value::Int(3), Value::Int(4)]);

        let result = builtin_set_symmetric_difference(&[a, b]).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.borrow().len(), 2); // {1, 4}
        } else {
            panic!("Expected array");
        }
    }

    #[test]
    fn test_set_is_subset() {
        let a = make_array(vec![Value::Int(1), Value::Int(2)]);
        let b = make_array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);

        let result = builtin_set_is_subset(&[a.clone(), b.clone()]).unwrap();
        assert_eq!(result, Value::Bool(true));

        let result_reverse = builtin_set_is_subset(&[b, a]).unwrap();
        assert_eq!(result_reverse, Value::Bool(false));
    }

    #[test]
    fn test_set_from_array_dedup() {
        let arr = make_array(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(1),
            Value::Int(3),
            Value::Int(2),
        ]);

        let result = builtin_set_from_array(&[arr]).unwrap();
        if let Value::Array(deduped) = result {
            assert_eq!(deduped.borrow().len(), 3); // {1, 2, 3}
        } else {
            panic!("Expected array");
        }
    }

    #[test]
    fn test_set_operations_with_strings() {
        let markets = make_array(vec![
            Value::String(SmolStr::new("NYSE")),
            Value::String(SmolStr::new("NASDAQ")),
            Value::String(SmolStr::new("LSE")),
        ]);
        let tech_exchanges = make_array(vec![
            Value::String(SmolStr::new("NASDAQ")),
            Value::String(SmolStr::new("TSE")),
        ]);

        let both = builtin_set_intersection(&[markets.clone(), tech_exchanges.clone()]).unwrap();
        if let Value::Array(arr) = both {
            assert_eq!(arr.borrow().len(), 1); // {"NASDAQ"}
            assert_eq!(
                arr.borrow()[0],
                Value::String(SmolStr::new("NASDAQ"))
            );
        } else {
            panic!("Expected array");
        }
    }

    // -- len builtin handles collections --

    #[test]
    fn test_len_works_on_hashmap() {
        let map = builtin_hashmap_new(&[]).unwrap();
        builtin_hashmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("k")),
            Value::Int(1),
        ])
        .unwrap();

        let len = builtin_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(1));
    }

    #[test]
    fn test_len_works_on_sortedmap() {
        let map = builtin_sortedmap_new(&[]).unwrap();
        builtin_sortedmap_insert(&[
            map.clone(),
            Value::String(SmolStr::new("k")),
            Value::Int(1),
        ])
        .unwrap();

        let len = builtin_len(&[map]).unwrap();
        assert_eq!(len, Value::Int(1));
    }

    // -- value_to_key conversion --

    #[test]
    fn test_value_to_key_conversions() {
        assert_eq!(
            value_to_key(&Value::String(SmolStr::new("hello"))).unwrap(),
            SmolStr::new("hello")
        );
        assert_eq!(
            value_to_key(&Value::Int(42)).unwrap(),
            SmolStr::new("42")
        );
        assert_eq!(
            value_to_key(&Value::Bool(true)).unwrap(),
            SmolStr::new("true")
        );
    }
}
