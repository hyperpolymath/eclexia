// SPDX-License-Identifier: MPL-2.0
// Invalid: echo_witness requires an Echo[A, B], not an Int.
//
// This must fail type checking — it exercises that Echo is a real type in
// the checker (unified structurally), not an ignored annotation.

fn main() {
    let bad = echo_witness(42)
    println(bad)
}
