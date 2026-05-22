// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Generic function with type parameter
// Expected: Success - generic types inferred correctly

fn identity<T>(x: T) -> T {
    x
}

fn main() {
    let int_val = identity(42);
    let str_val = identity("hello");
    let bool_val = identity(true);

    assert(int_val == 42);
    assert(bool_val == true);
}
