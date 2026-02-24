// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Adaptive block with two valid solutions
// Expected: Success - selects optimal solution based on shadow prices

adaptive fn compute(x: int) -> int {
    fast @requires(energy: 100J, time: 1ms) {
        // Fast but energy-intensive
        x * 2
    }

    slow @requires(energy: 10J, time: 10ms) {
        // Slow but energy-efficient
        x * 2
    }
}

fn main() {
    let result = compute(42);
    assert(result == 84);
}
