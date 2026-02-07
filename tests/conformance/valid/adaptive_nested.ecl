// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Nested adaptive blocks
// Expected: Success - both levels select optimal solutions

adaptive fn inner(x: int) -> int {
    fast @requires(energy: 10J) { x * 2 }
    slow @requires(energy: 5J) { x + x }
}

adaptive fn outer(x: int) -> int {
    fast @requires(energy: 50J) {
        inner(x) + inner(x)
    }

    slow @requires(energy: 20J) {
        let a = inner(x);
        let b = inner(x);
        a + b
    }
}

fn main() {
    let result = outer(10);
    assert(result == 40);
}
