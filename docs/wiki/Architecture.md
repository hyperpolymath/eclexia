# Architecture

## Compiler Pipeline

High-level flow:

1. Lexer
2. Parser
3. Type checker
4. HIR lowering
5. MIR lowering and optimization
6. Code generation and execution backends

## Runtime Model

The runtime centers on:

- resource tracking
- shadow-price-informed decision logic
- adaptive strategy selection
- scheduler/profiler/carbon modules

## Backends

- VM bytecode path
- LLVM path
- Cranelift path
- WASM path

## Deep-Dive References

- [`../../TOOLCHAIN_STATUS.md`](../../TOOLCHAIN_STATUS.md)
- [`../../ALGORITHMS.md`](../../ALGORITHMS.md)
- [`../architecture/MULTICOMPILER-ARCHITECTURE.md`](../architecture/MULTICOMPILER-ARCHITECTURE.md)
- [`../architecture/DESIGN-DECISIONS.adoc`](../architecture/DESIGN-DECISIONS.adoc)
