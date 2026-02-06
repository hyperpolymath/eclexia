# Eclexia Conformance Corpus

This directory contains the conformance test suite for Eclexia implementations.

## Structure

```
conformance/
├── valid/      # Programs that MUST succeed
└── invalid/    # Programs that MUST fail with deterministic errors
```

## Valid Tests

Programs in `valid/` must:
- Parse without errors
- Type check successfully
- Execute without constraint violations
- Produce expected output

| Test | Resources Tested | Description |
|------|------------------|-------------|
| `resource_typed_hello.ecl` | energy | Basic resource annotation |
| `energy_constraint_satisfied.ecl` | energy | Function calls within budget |
| `time_constraint_satisfied.ecl` | time | Latency constraints |
| `adaptive_solution_selection.ecl` | energy, time | Optimal solution selection |
| `energy_and_time_combined.ecl` | energy, time | Multi-resource tracking |

## Invalid Tests

Programs in `invalid/` must:
- Fail with a `ResourceViolation` error
- Produce deterministic, reproducible failures
- Include the violated constraint in the error message

| Test | Violation Type | Description |
|------|----------------|-------------|
| `energy_constraint_violation.ecl` | energy | Exceeds energy budget |
| `time_constraint_violation.ecl` | time | Exceeds latency budget |
| `no_valid_solution.ecl` | selection | No solution satisfies all constraints |
| `budget_exhaustion.ecl` | energy | Cumulative usage exceeds budget |
| `carbon_constraint_violation.ecl` | carbon | Exceeds carbon budget |

## Running Tests

```bash
# Run valid tests (should all succeed)
for f in tests/conformance/valid/*.ecl; do
    cargo run -- run "$f"
done

# Run invalid tests (should all fail with ResourceViolation)
for f in tests/conformance/invalid/*.ecl; do
    cargo run -- run "$f" && echo "ERROR: $f should have failed"
done
```

## Conformance Requirements

Per SPEC.core.scm, a conforming implementation must:

1. **Track resources**: At minimum, time and energy
2. **Reject violations**: `@requires` violations produce deterministic errors
3. **Dimensional analysis**: Reject dimension mismatches at type-check time
4. **Adaptive selection**: Select solution by minimizing weighted cost
5. **Deterministic errors**: Same input → same error, always

## Adding Tests

New tests should:
1. Include SPDX license header
2. Document expected behavior in comments
3. Test a single conformance requirement
4. Be minimal (smallest possible example)
