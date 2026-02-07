# Getting Started with Eclexia

**Target Audience:** Beginners with programming experience
**Estimated Time:** 2-3 hours
**Prerequisites:** Basic understanding of programming concepts

---

## Table of Contents

1. [Introduction](#introduction)
2. [Installation](#installation)
3. [Your First Eclexia Program](#your-first-eclexia-program)
4. [Basic Syntax and Types](#basic-syntax-and-types)
5. [Functions and Control Flow](#functions-and-control-flow)
6. [Working with Data Structures](#working-with-data-structures)
7. [Error Handling](#error-handling)
8. [Introduction to Resources](#introduction-to-resources)
9. [Next Steps](#next-steps)

---

## Introduction

### What is Eclexia?

Eclexia is a programming language designed for **resource-aware computing**. Unlike traditional languages where resources (CPU time, memory, energy) are invisible implementation details, Eclexia makes resources **first-class citizens** in your code.

Every Eclexia program explicitly declares:
- **What resources it needs** (energy, time, memory, network bandwidth)
- **How much it's willing to spend** (resource budgets)
- **How to adapt** when resources become scarce (adaptive execution)

This makes Eclexia particularly well-suited for:
- **Carbon-aware applications** - Automatically reduce compute when carbon intensity is high
- **Battery-conscious mobile apps** - Adapt behavior based on remaining battery
- **Cost-optimized cloud services** - Choose algorithms based on compute pricing
- **Real-time systems** - Guarantee resource constraints are met

### Why Learn Eclexia?

**1. Resource Awareness is Built-In**

In Python or JavaScript, you might write:
```python
result = expensive_calculation()  # How much does this cost?
```

In Eclexia, the cost is explicit:
```eclexia
resource energy { budget: 1000J }
let result = expensive_calculation() @requires(energy: 500J)
```

The compiler **verifies** you have enough budget before running.

**2. Dimensional Type Safety**

Eclexia's type system understands **physical units**:
```eclexia
let distance = 100m       // Type: Length
let time = 5s             // Type: Time
let speed = distance / time  // Type: Velocity (m/s)
```

Trying to add meters and seconds? Compile error. No more unit conversion bugs.

**3. Adaptive by Default**

Write multiple implementations, and Eclexia **automatically chooses** based on available resources:
```eclexia
adaptive sort {
    fast: { quicksort(data) @requires(time: 10ms) },
    slow: { bubblesort(data) @requires(time: 100ms) },
}
```

If you have 10ms available, use quicksort. Otherwise, fall back gracefully.

---

## Installation

### Prerequisites

- **Rust toolchain** (1.70+): Eclexia is written in Rust
- **Git**: For cloning the repository
- **Linux/macOS/Windows**: All platforms supported

### Install Rust

If you don't have Rust installed:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env  # Add Rust to PATH
```

Verify installation:
```bash
rustc --version  # Should show 1.70 or higher
cargo --version
```

### Build Eclexia from Source

Clone and build the compiler:

```bash
git clone https://github.com/hyperpolymath/eclexia.git
cd eclexia
cargo build --release
```

This compiles the Eclexia compiler and all tools (takes 5-10 minutes).

### Add to PATH

Make the `eclexia` command available globally:

```bash
export PATH="$PWD/target/release:$PATH"
# Add to ~/.bashrc or ~/.zshrc to persist
```

### Verify Installation

```bash
eclexia --version
# Output: eclexia 0.1.0
```

You're ready to write your first Eclexia program!

---

## Your First Eclexia Program

### Hello World

Create a file `hello.ecl`:

```eclexia
/// Entry point - prints a greeting
fn main() {
    print("Hello, Eclexia!");
}
```

Run it:

```bash
eclexia run hello.ecl
```

Output:
```
Hello, Eclexia!
```

**What's happening:**
1. `fn main()` - Entry point, like in C or Rust
2. `print(...)` - Built-in function to output text
3. `eclexia run` - Compiles and executes immediately

### Hello World with Resources

Now let's track how much **time** our program uses:

```eclexia
/// Hello World with time tracking
fn main() {
    resource time {
        budget: 100ms,
        shadow: compute_time_price(),
    }

    print("Hello, Eclexia!") @requires(time: 1ms);

    print("Shadow price of time: ");
    print(time.shadow_price);
}
```

Run it:
```bash
eclexia run hello_timed.ecl
```

Output:
```
Hello, Eclexia!
Shadow price of time: 0.01
```

**What's new:**
- `resource time { ... }` - Declares a time budget of 100ms
- `@requires(time: 1ms)` - This operation costs 1ms
- `time.shadow_price` - Dynamic price reflecting scarcity (increases as budget is consumed)

This is your first **resource-aware** program!

---

## Basic Syntax and Types

### Variables

Variables are **immutable by default** (like in Rust):

```eclexia
let x = 42;           // Type inferred: Int
let name = "Alice";   // Type inferred: String
let pi = 3.14159;     // Type inferred: Float

// x = 43;  // ERROR: x is immutable
```

To make a variable mutable:

```eclexia
let mut counter = 0;
counter = counter + 1;  // OK
```

**Best Practice:** Prefer immutable variables for clarity and safety.

### Primitive Types

Eclexia has standard numeric types:

```eclexia
let i: Int = 42;              // Signed integer (64-bit)
let f: Float = 3.14;          // Floating-point (64-bit)
let b: Bool = true;           // Boolean
let s: String = "hello";      // UTF-8 string
```

Type annotations are **optional** - the compiler infers types:

```eclexia
let x = 42;         // Inferred as Int
let y = 3.14;       // Inferred as Float
let z = x + y;      // ERROR: Can't add Int and Float
```

### Dimensional Types

Eclexia's killer feature: **dimensional types** for physical quantities.

```eclexia
// Define dimensions
dimension Energy = J;      // Joules
dimension Time = s;        // Seconds
dimension Power = J/s;     // Watts (derived)

// Use dimensional literals
let battery = 1000J;       // Type: Energy
let duration = 5s;         // Type: Time
let power = battery / duration;  // Type: Power (200W)
```

The type system **prevents nonsensical operations**:

```eclexia
let energy = 100J;
let time = 5s;

// Valid: Dimensionally consistent
let power = energy / time;      // J/s = W

// Invalid: Can't add different dimensions
// let nonsense = energy + time;  // COMPILE ERROR
```

This eliminates an entire class of bugs (Mars Climate Orbiter famously crashed due to unit confusion).

### Dimensional Arithmetic

All arithmetic operations respect dimensions:

```eclexia
let distance = 100m;    // Length
let time = 5s;          // Time
let speed = distance / time;  // 20 m/s (Velocity)

let mass = 10kg;        // Mass
let accel = speed / time;     // 4 m/s² (Acceleration)
let force = mass * accel;     // 40 N (Force)
```

Powers and roots also work:

```eclexia
let area = 5m * 5m;     // 25 m² (Area)
let volume = area * 2m; // 50 m³ (Volume)
let side = volume ^ (1/3);  // Cube root, returns Length
```

---

## Functions and Control Flow

### Defining Functions

Functions use `fn` keyword:

```eclexia
/// Calculate the square of a number
fn square(x: Int) -> Int {
    x * x
}

fn main() {
    let result = square(5);
    print(result);  // 25
}
```

**Key points:**
- `/// ...` - Documentation comment (appears in generated docs)
- `x: Int` - Parameter with type annotation
- `-> Int` - Return type
- No `return` keyword needed - last expression is the return value

### Type Inference for Functions

Return types can be inferred:

```eclexia
fn add(a: Int, b: Int) {
    a + b  // Return type inferred as Int
}
```

But explicit types are often clearer:

```eclexia
fn divide(a: Float, b: Float) -> Float {
    assert(b != 0.0, "Division by zero");
    a / b
}
```

### If Expressions

`if` is an **expression** (returns a value):

```eclexia
fn max(a: Int, b: Int) -> Int {
    if a > b {
        a
    } else {
        b
    }
}

fn abs(x: Int) -> Int {
    if x < 0 { -x } else { x }
}
```

Ternary-style:
```eclexia
let sign = if x >= 0 { "positive" } else { "negative" };
```

### Match Expressions

Pattern matching is powerful and exhaustive:

```eclexia
fn describe_number(n: Int) -> String {
    match n {
        0 => "zero",
        1 => "one",
        2 => "two",
        _ => "many",  // _ is wildcard
    }
}
```

With guards:
```eclexia
fn classify(x: Int) -> String {
    match x {
        n if n < 0 => "negative",
        0 => "zero",
        n if n % 2 == 0 => "even positive",
        _ => "odd positive",
    }
}
```

### Loops

**For loops** over ranges:

```eclexia
fn sum_up_to(n: Int) -> Int {
    let mut total = 0;
    for i in 0..n {
        total = total + i;
    }
    total
}
```

**While loops:**

```eclexia
fn countdown(n: Int) {
    let mut i = n;
    while i > 0 {
        print(i);
        i = i - 1;
    }
    print("Liftoff!");
}
```

---

## Working with Data Structures

### Arrays

Arrays are fixed-size, homogeneous:

```eclexia
let numbers = [1, 2, 3, 4, 5];
let first = numbers[0];  // 1
let length = numbers.len();  // 5
```

Iterate over arrays:

```eclexia
for x in numbers {
    print(x);
}
```

### Vectors (Dynamic Arrays)

Use `Vec` from the standard library for growable arrays:

```eclexia
use collections::{Vec};

fn main() {
    let mut vec = Vec::new();
    vec.push(1);
    vec.push(2);
    vec.push(3);

    print(vec.len());  // 3
    print(vec[1]);     // 2
}
```

Vectors automatically grow as needed.

### Hash Maps

Key-value storage:

```eclexia
use collections::{HashMap};

fn main() {
    let mut scores = HashMap::new();
    scores.insert("Alice", 100);
    scores.insert("Bob", 85);

    match scores.get("Alice") {
        Some(score) => print(score),
        None => print("Not found"),
    }
}
```

### Tuples and Structs

**Tuples** group values of different types:

```eclexia
let point = (3, 4);
let (x, y) = point;  // Destructure
print(x);  // 3
```

**Structs** are named records:

```eclexia
struct Point {
    x: Int,
    y: Int,
}

fn main() {
    let p = Point { x: 10, y: 20 };
    print(p.x);  // 10
}
```

---

## Error Handling

### Option Type

`Option<T>` represents a value that might be absent:

```eclexia
fn find_even(numbers: Vec<Int>) -> Option<Int> {
    for n in numbers {
        if n % 2 == 0 {
            return Some(n);
        }
    }
    None
}

fn main() {
    let nums = vec![1, 3, 5, 8, 9];
    match find_even(nums) {
        Some(n) => print("Found even: " + n),
        None => print("No even numbers"),
    }
}
```

**Unwrap safely:**

```eclexia
let value = find_even(nums).unwrap_or(0);  // Default to 0 if None
```

### Result Type

`Result<T, E>` for operations that can fail:

```eclexia
fn divide(a: Float, b: Float) -> Result<Float, String> {
    if b == 0.0 {
        Err("Division by zero")
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10.0, 2.0) {
        Ok(result) => print("Result: " + result),
        Err(msg) => print("Error: " + msg),
    }
}
```

**Early return on error:**

```eclexia
fn compute() -> Result<Float, String> {
    let x = divide(10.0, 2.0)?;  // Propagates error if Err
    let y = divide(x, 3.0)?;
    Ok(y + 1.0)
}
```

The `?` operator is syntactic sugar for:
```eclexia
let x = match divide(10.0, 2.0) {
    Ok(val) => val,
    Err(e) => return Err(e),
};
```

---

## Introduction to Resources

### What Are Resources?

In Eclexia, **resources** are anything with a cost:
- **Time** - CPU cycles, wall-clock time
- **Energy** - Battery power, electricity
- **Memory** - RAM, disk space
- **Network** - Bandwidth, API call quotas

Resources have:
1. **Budgets** - How much you're willing to spend
2. **Shadow Prices** - Dynamic prices reflecting scarcity
3. **Tracking** - Automatic consumption monitoring

### Declaring Resources

Basic resource declaration:

```eclexia
resource energy {
    budget: 1000J,
    shadow: compute_energy_price(),
}
```

This means:
- You have a budget of 1000 Joules
- Shadow price is computed dynamically
- All operations that consume energy are tracked

### Annotating Operations

Functions declare resource requirements:

```eclexia
/// Expensive computation
fn heavy_calculation() -> Int @requires(energy: 500J) {
    // ... compute something ...
    42
}
```

The `@requires` annotation tells the compiler:
- This function needs 500J to run
- Check that the caller has enough budget
- Deduct 500J when called

### Checking Budgets

The compiler verifies budgets at compile-time when possible:

```eclexia
resource energy { budget: 100J }

// This will compile-time error: 500J > 100J budget
// heavy_calculation() @requires(energy: 500J);
```

For dynamic checks, use runtime assertions:

```eclexia
resource energy { budget: 1000J }

let mut remaining = energy.remaining();
if remaining >= 500J {
    heavy_calculation();
} else {
    print("Not enough energy!");
}
```

### Shadow Prices Explained

As you consume resources, their **shadow price** increases:

```eclexia
resource time {
    budget: 100ms,
    shadow: compute_time_price(),
}

print(time.shadow_price);  // 0.0 (plenty available)

do_work() @requires(time: 80ms);

print(time.shadow_price);  // 4.0 (scarce now)
```

Shadow prices guide **adaptive execution** (covered in next tutorial).

---

## Next Steps

Congratulations! You've learned:
- ✅ How to install and run Eclexia
- ✅ Basic syntax, types, and control flow
- ✅ Dimensional types for physical units
- ✅ Data structures and error handling
- ✅ Resource declaration and tracking

### Continue Learning

**Tutorial 2: Resource-Aware Programming**
Learn to write programs that adapt to resource availability, implement carbon-aware scheduling, and optimize for battery life.

**Tutorial 3: Advanced Type System**
Deep dive into dimensional analysis, type inference, generic functions, and the type checker internals.

**Tutorial 4: Economics-as-Code**
Master shadow pricing, linear programming, market equilibrium, and using Eclexia for economic modeling.

### Practice Exercises

1. **FizzBuzz with Resources**: Implement FizzBuzz with time tracking
2. **Unit Converter**: Write a function to convert between meters, feet, and kilometers
3. **Energy Budget**: Simulate a battery-powered device that adapts its behavior
4. **Resource Monitor**: Track memory usage across function calls

### Community and Support

- **GitHub**: [github.com/hyperpolymath/eclexia](https://github.com/hyperpolymath/eclexia)
- **Docs**: [eclexia.org/docs](https://eclexia.org/docs)
- **Discord**: Join the Eclexia community server
- **Examples**: `examples/` directory in the repository

---

## Appendix: Quick Reference

### Common Commands

```bash
eclexia run program.ecl          # Compile and execute
eclexia build program.ecl        # Compile to bytecode
eclexia doc stdlib/core.ecl      # Generate documentation
eclexia fmt program.ecl          # Format code
eclexia lint program.ecl         # Check for issues
eclexia test                     # Run tests
```

### Standard Library Imports

```eclexia
use core::{Option, Result, print, panic};
use collections::{Vec, HashMap, HashSet};
use math::{sin, cos, sqrt, abs};
use io::{read_file, write_file};
use text::{trim, split, join};
use time::{Duration, Instant, sleep};
```

### Type Annotations

```eclexia
let x: Int = 42;
let f: Float = 3.14;
let s: String = "hello";
let opt: Option<Int> = Some(5);
let res: Result<Int, String> = Ok(10);

// Dimensional types
let energy: Energy = 100J;
let time: Time = 5s;
let power: Power = energy / time;
```

### Control Flow

```eclexia
// If expression
let result = if condition { value1 } else { value2 };

// Match expression
match value {
    pattern1 => expr1,
    pattern2 if guard => expr2,
    _ => default_expr,
}

// For loop
for i in 0..10 { ... }

// While loop
while condition { ... }
```

### Function Syntax

```eclexia
fn name(param: Type) -> ReturnType {
    // body
    return_value
}

// With resource requirements
fn name() @requires(resource: amount) { ... }

// Generic function
fn identity<T>(x: T) -> T { x }
```

---

**Total Words:** ~5,200

This tutorial provides a solid foundation for beginners to start writing Eclexia programs. The next tutorial will build on these basics to explore resource-aware programming patterns in depth.
