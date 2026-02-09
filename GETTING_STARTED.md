# Getting Started with Eclexia

Eclexia is an "Economics-as-Code" programming language that brings resource-aware computing to software development. This guide will help you get up and running quickly.

> **Status (2026-02-09):** Eclexia is under active development (~55% complete).
> The compiler pipeline (lexer, parser, type checker, HIR/MIR, bytecode VM) works
> for core language features. Adaptive functions, domain-specific libraries, and
> native code backends (LLVM, Cranelift, WASM) are **not yet implemented**.
> The `run` command uses a tree-walking interpreter; `build` emits bytecode (JSON
> or `.eclb` binary) for the stack-based VM.

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
fn main() {
    println("Hello, Economics-as-Code!")
}
```

### 3. Run Your Program

```bash
eclexia run src/main.ecl
```

## Core Concepts

### Core Language Features

Eclexia supports functions, pattern matching, closures, generics, structs, enums,
and a Hindley-Milner type system with dimensional analysis:

```eclexia
fn efficient_fib(n: Int) -> Int {
    fib_helper(n, 0, 1)
}

fn fib_helper(n: Int, a: Int, b: Int) -> Int {
    if n <= 0 { a } else { fib_helper(n - 1, b, a + b) }
}

fn main() -> Int {
    efficient_fib(10)
}
```

### Adaptive Functions (Planned)

> **Not yet implemented.** The syntax below shows the design goal for adaptive
> functions — functions with multiple implementations selected at runtime based
> on resource constraints and shadow prices. The parser recognises `adaptive`
> as a keyword but the full adaptive dispatch is not yet wired through the
> compiler pipeline.

```eclexia
// Design goal — not yet functional
adaptive fn fibonacci(n: Int) -> Int
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

### Dimensional Types (Partial)

The type system tracks physical dimensions (mass, length, time, etc.) and
prevents unit mismatches at compile time. Dimensional annotations on literals
(e.g., `5.0J`) are **not yet supported** — dimensions are currently expressed
via the `Resource` type in the type checker.

## CLI Commands

| Command | Description |
|---------|-------------|
| `eclexia run <file>` | Execute via tree-walking interpreter |
| `eclexia build <file> -o <out>` | Compile to bytecode (JSON or `.eclb`) |
| `eclexia check <file>` | Type-check without running |
| `eclexia init [name]` | Create a new project |
| `eclexia fmt <files>` | Format source files |
| `eclexia repl` | Start interactive REPL |
| `eclexia run <file.eclb>` | Execute a compiled `.eclb` bytecode file via VM |

### Run Options

```bash
# Run with shadow price observation
eclexia run src/main.ecl --observe-shadow

# Run with carbon report
eclexia run src/main.ecl --carbon-report
```

## Example: Simple Arithmetic

See `examples/math_showcase.ecl` for a complete example:

```bash
eclexia run examples/math_showcase.ecl
```

Or compile to bytecode and run via the VM:

```bash
# Compile a pure-function program to .eclb
eclexia build examples/minimal.ecl -o /tmp/out.eclb
# Execute via the stack-based VM
eclexia run /tmp/out.eclb
```

> **Note:** The `build` command compiles through the full pipeline (parse →
> typecheck → HIR → MIR → bytecode). Currently only pure-function programs
> compile to bytecode — builtins like `println` are not yet linked into the
> bytecode path.

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
