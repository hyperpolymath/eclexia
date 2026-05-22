// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Closure capturing resource-annotated values
// Expected: Success

fn main() {
    let x = 42;
    let closure = |y| x + y;
    let result = closure(10);
    assert(result == 52);
}
