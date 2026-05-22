// SPDX-License-Identifier: MPL-2.0

// Test: Higher-order functions
fn apply(f: fn(int) -> int, x: int) -> int {
    f(x)
}

fn double(x: int) -> int { x * 2 }

fn main() {
    let result = apply(double, 21);
    assert(result == 42);
}
