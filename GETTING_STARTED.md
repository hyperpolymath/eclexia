# Getting Started with Eclexia

Eclexia is an "Economics-as-Code" programming language that brings resource-aware computing to software development. This guide will help you get up and running quickly.

## Installation

### Prerequisites

- Rust 1.75 or later
- Cargo (comes with Rust)

### Building from Source

```bash
git clone https://github.com/hyperpolymath/eclexia.git
cd eclexia
cargo build --release
```

The binary will be available at `target/release/eclexia`.

## Quick Start

### 1. Create a New Project

```bash
eclexia init my-project
cd my-project
```

This creates a new Eclexia project with:
- `eclexia.toml` - Project configuration
- `src/main.ecl` - Entry point

### 2. Write Your First Program

Edit `src/main.ecl`:

```eclexia
// A simple hello world program
def main() -> Unit {
    println("Hello, Economics-as-Code!")
}
```

### 3. Run Your Program

```bash
eclexia run src/main.ecl
```

## Core Concepts

### Adaptive Functions

Eclexia's key innovation is **adaptive functions** - functions with multiple implementations that the runtime selects based on resource constraints.

```eclexia
// Define helper functions
def efficient_fib(n: Int) -> Int {
    fib_helper(n, 0, 1)
}

def fib_helper(n: Int, a: Int, b: Int) -> Int {
    if n <= 0 { a } else { fib_helper(n - 1, b, a + b) }
}

def simple_fib(n: Int) -> Int {
    if n <= 1 { n } else { simple_fib(n - 1) + simple_fib(n - 2) }
}

// Adaptive function with multiple solutions
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "efficient":
        @when: true
        @provides: energy: 5J, latency: 10ms, carbon: 1gCO2e
    {
        efficient_fib(n)
    }

    @solution "naive":
        @when: true
        @provides: energy: 50J, latency: 50ms, carbon: 5gCO2e
    {
        simple_fib(n)
    }
}
```

The runtime uses **shadow prices** to select the optimal solution based on:
- Energy consumption (Joules)
- Latency (milliseconds)
- Carbon emissions (gCO2e)

### Resource Annotations

Functions can declare resource constraints:

```eclexia
def process_data() -> Unit
    @requires: energy < 10J
    @requires: carbon < 5gCO2e
{
    // Implementation
}
```

### Dimensional Types

Eclexia supports SI units at the type level:

```eclexia
let energy: Float<J> = 5.0J        // Joules
let power: Float<W> = 100.0W       // Watts
let carbon: Float<gCO2e> = 2.5gCO2e  // Carbon emissions
```

## CLI Commands

| Command | Description |
|---------|-------------|
| `eclexia run <file>` | Execute an Eclexia program |
| `eclexia build <file>` | Compile a program |
| `eclexia check <file>` | Type-check without running |
| `eclexia init [name]` | Create a new project |
| `eclexia fmt <files>` | Format source files |
| `eclexia repl` | Start interactive REPL |

### Run Options

```bash
# Run with shadow price observation
eclexia run src/main.ecl --observe-shadow

# Run with carbon report
eclexia run src/main.ecl --carbon-report
```

## Example: Adaptive Fibonacci

See `examples/fibonacci.ecl` for a complete example:

```bash
eclexia run examples/fibonacci.ecl
```

Output:
```
Eclexia Adaptive Fibonacci Demo
================================
  [adaptive] Selected solution 'efficient' for fibonacci

fibonacci(10) = 55

The runtime selected the best solution based on shadow prices:
  efficient: cost = 5 + 10 + 1 = 16
  naive:     cost = 50 + 50 + 5 = 105
```

## Project Configuration

The `eclexia.toml` file configures your project:

```toml
[package]
name = "my-project"
version = "0.1.0"
edition = "2025"

[dependencies]
# Add dependencies here

[resources]
default-energy-budget = "1000J"
default-carbon-budget = "100gCO2e"
```

## Error Messages

Eclexia provides helpful error messages with source locations:

```
Type errors:
  3:16: type mismatch: expected Int, found String
```

## Next Steps

- Read the [Specification](SPECIFICATION.md) for language details
- Explore the [Theory](THEORY.md) for the economics foundation
- Check the [Implementation Roadmap](IMPLEMENTATION_ROADMAP.md) for upcoming features
- Browse `examples/` for more code samples

## Getting Help

- [GitHub Issues](https://github.com/hyperpolymath/eclexia/issues)
- [Contributing Guide](CONTRIBUTING.md)
