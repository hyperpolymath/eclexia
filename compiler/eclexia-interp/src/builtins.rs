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
            got: args.len(),
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
            got: args.len(),
        });
    }

    Ok(Value::String(SmolStr::new(format!("{}", args[0]))))
}

fn builtin_abs(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 1 {
        return Err(RuntimeError::ArityMismatch {
            expected: 1,
            got: args.len(),
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
            got: args.len(),
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
            got: args.len(),
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
            got: args.len(),
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
            got: args.len(),
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
            got: args.len(),
        });
    }

    match &args[0] {
        Value::Float(f) => Ok(Value::Int(f.ceil() as i64)),
        Value::Int(n) => Ok(Value::Int(*n)),
        other => Err(RuntimeError::type_error("numeric", other.type_name())),
    }
}

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
                got: args.len(),
            })
        }
    };

    let values: Vec<Value> = (start..end).map(Value::Int).collect();
    Ok(Value::Array(std::rc::Rc::new(std::cell::RefCell::new(
        values,
    ))))
}

fn builtin_push(args: &[Value]) -> RuntimeResult<Value> {
    if args.len() != 2 {
        return Err(RuntimeError::ArityMismatch {
            expected: 2,
            got: args.len(),
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
            got: args.len(),
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
