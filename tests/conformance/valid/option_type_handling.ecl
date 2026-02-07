// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Option type operations
fn safe_divide(a: int, b: int) -> Option<int> {
    if b == 0 {
        None
    } else {
        Some(a / b)
    }
}

fn main() {
    let result = safe_divide(10, 2);
    assert(result.is_some());
    assert(result.unwrap() == 5);
    
    let error = safe_divide(10, 0);
    assert(error.is_none());
}
