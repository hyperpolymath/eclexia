// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Basic type inference
// Expected: Success - types inferred correctly

fn main() {
    let x = 42;           // Inferred as int
    let y = 3.14;         // Inferred as float
    let z = "hello";      // Inferred as string
    let b = true;         // Inferred as bool

    let sum = x + x;      // int + int = int
    let product = y * 2.0;  // float * float = float

    assert(sum == 84);
}
