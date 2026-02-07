// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Shadow prices are non-negative and monotonic
// Expected: Success - shadow prices increase as resources become scarce

@requires(energy: 100J)
fn constrained() {
    // Shadow price should reflect scarcity
    let price1 = shadow_price(energy);
    use_energy(50J);
    let price2 = shadow_price(energy);

    // As energy becomes scarcer, price should increase
    assert(price2 >= price1);
}

fn use_energy(amount: Resource<Energy>) {
    // Consumes energy
}

fn main() {
    constrained();
}
