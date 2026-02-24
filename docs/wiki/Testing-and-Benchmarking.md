# Testing and Benchmarking

## Testing Layers

- Unit tests: crate-level correctness
- Conformance tests: language behavior guarantees
- Integration tests: cross-component behavior
- Point-to-point checks: interop and boundary verification
- End-to-end checks: program execution flows through CLI/runtime

## Recommended Local Gate

```bash
just fmt-check
just lint
just test-unit
just test-conformance
just test-integration
just test-p2p
just test-e2e
just bench-smoke
```

## Benchmarking

Use benchmark smoke tests for regression detection and dedicated benchmarks for deeper performance studies.

```bash
just bench-smoke
```

## Security and Analysis

```bash
just panic-attack
```

If `panic-attack` is unavailable in your environment, install it and rerun.
