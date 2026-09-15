// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Resource overflow in nested calls
// Expected: ResourceViolation - cumulative usage exceeds budget
//
// ADR-001 2.2.1 note: this fixture used to force the overflow by calling a
// plain `def`/`fn` whose `@requires` ceiling alone was charged to the caller
// as a point cost, even though the callee's body did no work. That was the
// bug ADR-001 rules out: `@requires` is a budget the callee promises not to
// exceed, not a cost it promises to incur. Under the corrected accounting,
// a plain `fn` with an empty body genuinely costs 0J, so overflow must now
// come from a genuine `@provides`-sourced charge — here, an adaptive
// function's solution declares its real per-call cost via the legacy
// `option @requires(energy: N)` sugar, which the interpreter's no-`@when`
// path stores as that solution's `.provides.energy` (see
// eval.rs call_value_inner, AdaptiveFunction / no-@when branch).

adaptive fn expensive() {
    only @requires(energy: 15J) {
        // Real per-call cost: 15J, charged via @provides on selection.
    }
}

@requires(energy: 25J)
fn caller() {
    expensive();  // Uses 15J
    expensive();  // Uses another 15J
    // Total: 30J, exceeds 25J budget - should fail
}

fn main() {
    caller();
}
