// SPDX-License-Identifier: MPL-2.0

// Test: Uninitialized variable usage
fn main() {
    let x: int;
    let y = x + 10;  // Should fail: x not initialized
}
