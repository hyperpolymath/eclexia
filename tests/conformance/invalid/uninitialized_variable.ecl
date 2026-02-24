// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Uninitialized variable usage
fn main() {
    let x: int;
    let y = x + 10;  // Should fail: x not initialized
}
