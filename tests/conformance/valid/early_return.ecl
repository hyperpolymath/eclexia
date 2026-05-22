// SPDX-License-Identifier: MPL-2.0

// Test: Early return from function
fn find_positive(arr: [int]) -> Option<int> {
    for x in arr {
        if x > 0 {
            return Some(x);
        }
    }
    None
}

fn main() {
    let result = find_positive([-1, -2, 3, 4]);
    assert(result.is_some());
}
