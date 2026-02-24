// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Nested loops with resource tracking
@requires(energy: 200J)
fn matrix_sum() -> int {
    let mut sum = 0;
    for i in 0..5 {
        for j in 0..5 {
            sum = sum + (i * j);
        }
    }
    sum
}

fn main() {
    let result = matrix_sum();
    assert(result > 0);
}
