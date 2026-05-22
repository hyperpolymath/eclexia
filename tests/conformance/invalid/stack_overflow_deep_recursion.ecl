// SPDX-License-Identifier: MPL-2.0

// Test: Stack overflow from deep recursion
fn infinite_recursion(n: int) -> int {
    infinite_recursion(n + 1)
}

fn main() {
    infinite_recursion(0);  // Should fail
}
