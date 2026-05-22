// SPDX-License-Identifier: MPL-2.0

// Test: Short-circuit evaluation
fn expensive() -> bool {
    // Expensive operation
    true
}

fn main() {
    let result = false && expensive();  // Should not call expensive()
    assert(result == false);
}
