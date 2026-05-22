// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Type mismatch in return value
// Expected: Type error - returning int when float expected

fn returns_float() -> float {
    42  // Should fail: int != float
}

fn main() {
    let x = returns_float();
}
