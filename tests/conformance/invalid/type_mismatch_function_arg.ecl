// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Type mismatch in function argument
// Expected: Type error - passing float to int parameter

fn takes_int(x: int) -> int {
    x * 2
}

fn main() {
    let result = takes_int(3.14);  // Should fail: float != int
}
