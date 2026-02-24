// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Higher-order functions
fn apply(f: fn(int) -> int, x: int) -> int {
    f(x)
}

fn double(x: int) -> int { x * 2 }

fn main() {
    let result = apply(double, 21);
    assert(result == 42);
}
