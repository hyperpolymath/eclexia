// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Resource overflow in nested calls
// Expected: ResourceViolation - cumulative usage exceeds budget

@requires(energy: 15J)
fn expensive() {
    // Uses 15J
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
