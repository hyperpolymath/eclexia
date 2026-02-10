// SPDX-License-Identifier: PMPL-1.0-or-later
// Module system demo.
// NOTE: Qualified paths (math::add) are not yet supported in expression parsing,
// and bytecode lowering ignores module items. Keep top-level duplicates for now.

module math {
    fn add(a: Int, b: Int) -> Int {
        a + b
    }

    fn mul(a: Int, b: Int) -> Int {
        a * b
    }
}

// Top-level duplicates for bytecode path (modules not lowered yet).
fn add(a: Int, b: Int) -> Int {
    a + b
}

fn mul(a: Int, b: Int) -> Int {
    a * b
}

fn main() {
    println("=== Module System Demo ===")

    let a = 6
    let b = 7
    println("add(a, b) =", add(a, b))
    println("mul(a, b) =", mul(a, b))
}
