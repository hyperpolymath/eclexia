// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Stack overflow from deep recursion
fn infinite_recursion(n: int) -> int {
    infinite_recursion(n + 1)
}

fn main() {
    infinite_recursion(0);  // Should fail
}
