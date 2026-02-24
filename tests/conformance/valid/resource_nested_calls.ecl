// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Resource tracking through nested function calls
// Expected: Success - cumulative resource usage tracked correctly

@requires(energy: 10J)
fn inner() {
    // Uses 10J
}

@requires(energy: 30J)
fn outer() {
    inner();  // Uses 10J
    inner();  // Uses another 10J
    // Total: 20J, within 30J budget
}

fn main() {
    outer();
}
