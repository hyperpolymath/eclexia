// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Short-circuit evaluation
fn expensive() -> bool {
    // Expensive operation
    true
}

fn main() {
    let result = false && expensive();  // Should not call expensive()
    assert(result == false);
}
