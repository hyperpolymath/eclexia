# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Eclexia System Specifications

**Version:** 1.0.0
**Date:** 2026-03-14

---

## 1. Memory Model

### 1.1 Runtime Representation

Eclexia values are heap-allocated Rust `enum Value` variants. The interpreter
uses `Rc<RefCell<T>>` for shared mutable state within a single thread.

```
Value storage:
  Scalars (Int, Float, Bool, Char, Unit)  — stack-allocated, Copy
  Strings                                 — heap-allocated, Rc<String>
  Arrays                                  — heap-allocated, Vec<Value> (mutable)
  Tuples                                  — heap-allocated, Vec<Value> (immutable)
  Structs                                 — heap-allocated, HashMap<String, Value>
  HashMaps/SortedMaps                     — heap-allocated, standard collections
  Functions/Closures                      — heap-allocated, captures environment Rc
  Resource values                         — stack f64 + dimension metadata
```

### 1.2 Environment Representation

```
Environment = Rc<RefCell<{
  bindings: FxHashMap<SmolStr, Value>,
  parent: Option<Rc<RefCell<Environment>>>
}>>
```

Child environments hold `Rc` reference to parent — forms a linked chain.
Variable lookup traverses this chain. No garbage collection needed beyond
Rust's reference counting (`Rc` drop when refcount reaches 0).

### 1.3 Ownership Model

- **Interpreter mode:** Reference-counted (`Rc<RefCell>`) — no borrow checker.
  Values are cloned on assignment. Arrays are mutable in-place via `RefCell`.
- **Compiled mode (WASM/LLVM):** Ownership follows target platform conventions.
  WASM uses linear memory with bump allocator. LLVM uses stack allocation
  for scalars, heap for aggregates.

### 1.4 Resource Memory

Resource tracking state (`energy_used`, `carbon_used`, shadow prices) is
stored in the interpreter's `Σ` state struct — a single mutable struct
threaded through evaluation. No heap allocation for resource tracking.

---

## 2. Concurrency Model

### 2.1 Async Runtime

Eclexia uses `tokio` for async execution:

```
Runtime = tokio::runtime::Runtime (multi-threaded)

Primitives:
  spawn(expr)      — tokio::spawn (returns TaskHandle)
  chan::<T>()       — tokio::sync::mpsc::unbounded_channel
  send(tx, value)  — tx.send(value)
  recv(rx)         — runtime.block_on(rx.recv())
  yield            — tokio::task::yield_now()
  select { arms }  — tokio::select!
```

### 2.2 Thread Safety

- Environment (`Rc<RefCell>`) is **not thread-safe** — each spawned task
  gets its own environment copy, not a shared reference.
- Channel values must be `Clone` (values are cloned when sent).
- No shared mutable state between tasks — message passing only.

### 2.3 Adaptive Function Concurrency

Adaptive functions may spawn multiple solutions concurrently and select
the best result. Each solution runs in its own task with independent
resource tracking. The selector merges results.

---

## 3. Effect System

### 3.1 Current State

Effects are **declared but not enforced** at the type level:

```
effect IO {
  print(s: String) -> Unit;
  read_line() -> String;
}

handle expr {
  IO::print(s) resume k => { /* handler */ }
}
```

### 3.2 Planned Enforcement

Future: effect rows tracked through the type system. Each function's type
includes its effect set. The `handle` expression eliminates effects from
the type, converting effectful computations to pure ones.

### 3.3 Resource Effects

Resource consumption is a *de facto* effect tracked through the interpreter
state `Σ`, not through the type system. The `@requires` annotation serves
as an effect declaration for resource consumption.

---

## 4. Module System

### 4.1 File-Based Modules

```
import std::collections::HashMap
import std::io::println
use mylib::utils::*
```

### 4.2 Visibility

```
pub fn public_function() { ... }    — visible outside module
fn private_function() { ... }       — module-internal only
pub(crate) fn crate_visible() { ... } — visible within crate
```

### 4.3 Module Resolution

1. Check local scope
2. Check imported names
3. Check wildcard imports (`use foo::*`)
4. Check built-in names

### 4.4 Package Manager

Eclexia has a package manager (`eclexia-pkg`) with:
- Manifest parsing (`eclexia.toml`)
- Dependency resolution (petgraph-based DAG)
- Registry integration
- Lock file generation
