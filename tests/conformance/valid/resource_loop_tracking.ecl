// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Resource tracking in loops
// Expected: Success - loop iterations tracked correctly

@requires(energy: 55J)
fn process_batch() {
    let mut total = 0;
    for i in 0..5 {
        // Each iteration uses ~10J
        total = total + i;
    }
    // Total: ~50J, within 55J budget
}

fn main() {
    process_batch();
}
