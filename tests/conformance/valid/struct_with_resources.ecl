// SPDX-License-Identifier: MPL-2.0

// Test: Struct types
struct Point { x: int, y: int }

fn main() {
    let p = Point { x: 10, y: 20 };
    assert(p.x == 10);
}
