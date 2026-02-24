// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Adaptive block with no feasible solution
// Expected: ResourceViolation - all solutions exceed budget

@requires(energy: 50J)
adaptive fn impossible() {
    option1 @requires(energy: 100J) {
        // Exceeds budget
    }

    option2 @requires(energy: 75J) {
        // Also exceeds budget
    }
}

fn main() {
    impossible();
}
