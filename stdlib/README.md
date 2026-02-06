# Eclexia Standard Library

The Eclexia standard library provides essential types, data structures, and functions for all Eclexia programs.

## Modules

### core.ecl
Core types and operations:
- **Option<T>**: Optional values (Some/None)
- **Result<T, E>**: Error handling (Ok/Err)
- **panic/assert**: Runtime assertions
- **print/println**: Console output
- **Array utilities**: len, get, push, pop
- **String utilities**: len, concat, substring
- **Conversions**: int_to_string, string_to_int, etc.

### collections.ecl
Data structures:
- **Vec<T>**: Dynamically-sized array
- **HashMap<K, V>**: Key-value hash table
- **HashSet<T>**: Set of unique values

### math.ecl
Mathematical functions:
- **Constants**: PI, E, TAU
- **Basic**: abs, min, max, pow, sqrt, cbrt
- **Trigonometry**: sin, cos, tan, asin, acos, atan, atan2
- **Hyperbolic**: sinh, cosh, tanh
- **Exponential**: exp, ln, log10, log2, log
- **Rounding**: floor, ceil, round, trunc
- **Number theory**: factorial, gcd, lcm
- **Utilities**: clamp

## Usage

```eclexia
import core::{Option, Result, panic}
import collections::{Vec, HashMap}
import math::{PI, sin, cos}

fn main() {
    // Option type
    let maybe_value = Some(42)
    let value = maybe_value.unwrap_or(0)

    // Result type
    let result: Result<Int, String> = Ok(100)
    match result {
        Ok(n) => println(n),
        Err(e) => panic(e),
    }

    // Collections
    let mut vec = Vec::new()
    vec.push(1)
    vec.push(2)
    vec.push(3)

    let mut map = HashMap::new()
    map.insert("key", "value")

    // Math
    let angle = PI / 2.0
    let result = sin(angle)  // Should be 1.0
}
```

## Builtin Functions

Some functions are marked with `@builtin("name")` - these are implemented directly by the compiler/runtime and not in Eclexia source code.

## Resource Awareness

The standard library is designed to work with Eclexia's resource-aware type system. Functions and data structures can declare resource constraints using `@requires` and `@provides` annotations.

## Future Additions

Planned additions to the stdlib:
- **io**: File I/O, network I/O
- **time**: Date/time handling
- **json**: JSON parsing/serialization
- **regex**: Regular expressions
- **crypto**: Cryptographic primitives
- **concurrent**: Concurrency primitives
