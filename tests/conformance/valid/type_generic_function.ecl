// SPDX-License-Identifier: PMPL-1.0-or-later
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
