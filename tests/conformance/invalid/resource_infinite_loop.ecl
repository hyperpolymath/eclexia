// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Resource exhaustion in infinite loop
// Expected: ResourceViolation - budget exhausted during infinite loop

@requires(energy: 100J)
fn infinite() {
    loop {
        // Each iteration uses energy
        let x = 42;
    }
    // Should fail: infinite loops will eventually exhaust any finite budget
}

fn main() {
    infinite();
}
