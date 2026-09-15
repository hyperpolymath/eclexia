// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Shadow prices are non-negative and monotonic
// Expected: Success - shadow prices increase as resources become scarce

@requires(energy: 100J)
fn constrained() {
    // Shadow price should reflect scarcity.
    // Resource names live in a separate namespace from term
    // variables (ADR-001 G1) and are never bound in a function
    // body, so the resource is named by its string literal here,
    // matching the idiom used in examples/resource_tracking.ecl.
    let price1 = shadow_price("energy");
    use_energy(50J);
    let price2 = shadow_price("energy");

    // As energy becomes scarcer, price should increase
    assert(price2 >= price1);
}

fn use_energy(amount: Resource<Energy>) {
    // Consumes energy
}

fn main() {
    constrained();
}
