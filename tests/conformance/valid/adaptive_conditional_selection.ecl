// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Adaptive selection with conditional logic
// Expected: Success - selection considers control flow

adaptive fn conditional(use_fast: bool) -> int {
    fast @requires(energy: 100J) {
        if use_fast {
            42
        } else {
            0
        }
    }

    slow @requires(energy: 10J) {
        if use_fast {
            0
        } else {
            42
        }
    }
}

fn main() {
    let result1 = conditional(true);
    let result2 = conditional(false);
    assert(result1 == 42);
    assert(result2 == 42);
}
