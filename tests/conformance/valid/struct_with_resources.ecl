// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Struct types
struct Point { x: int, y: int }

fn main() {
    let p = Point { x: 10, y: 20 };
    assert(p.x == 10);
}
