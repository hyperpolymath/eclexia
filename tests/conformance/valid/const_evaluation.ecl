// SPDX-License-Identifier: MPL-2.0

// Test: Compile-time constant evaluation
const MAX: int = 100;
const DOUBLE_MAX: int = MAX * 2;

fn main() {
    assert(DOUBLE_MAX == 200);
}
