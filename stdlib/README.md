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
- **SortedMap<K, V>**: Ordered key-value map
- **Queue<T>**: FIFO queue
- **PriorityQueue<T>**: Priority-based queue
- **Set operations**: union, intersection, difference

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

### io.ecl
I/O operations:
- **File I/O**: read_file, write_file, file_exists
- **JSON**: parse_json, to_json, read_json, write_json
- **Economics use case**: Reading carbon intensity data, saving optimization results

Example:
```eclexia
import io::{read_file, write_json}

fn save_carbon_report(data: Value) {
    write_json("carbon_report.json", data)
}
```

### text.ecl
Text and string manipulation:
- **Basic**: trim, split, contains, length
- **Case conversion**: to_lowercase, to_uppercase
- **Pattern matching**: replace, starts_with, ends_with
- **Joining**: join (array of strings)

Example:
```eclexia
import text::{split, trim, to_lowercase}

fn parse_csv_line(line: String) -> [String] {
    let parts = split(line, ",")
    // Trim and lowercase each part
    parts
}
```

### time.ecl
Time and duration utilities:
- **Types**: Duration, Instant, DateTime
- **Current time**: now, now_ms, unix_timestamp
- **Timing**: sleep, measure, elapsed
- **Datetime**: hour, day_of_week, to_iso8601, from_iso8601
- **Economics use case**: Carbon-aware scheduling based on time of day

Example:
```eclexia
import time::{now, elapsed, hour, day_of_week}

fn is_low_carbon_period() -> Bool {
    let current_hour = hour()
    let day = day_of_week()

    // Weekends and off-peak hours (22:00-06:00)
    (day == 0 || day == 6) || (current_hour >= 22 || current_hour < 6)
}

fn time_operation<T>(f: fn() -> T) -> T {
    let start = now()
    let result = f()
    let duration = elapsed(start)
    println("Operation took: " + to_string(as_millis(duration)) + "ms")
    result
}
```

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
- **network**: HTTP client, TCP/UDP sockets
- **regex**: Regular expressions
- **crypto**: Cryptographic primitives
- **concurrent**: Concurrency primitives (async/await, channels)
- **testing**: Property-based testing, benchmarking utilities
- **serialization**: MessagePack, CBOR, Protocol Buffers
