// SPDX-License-Identifier: MPL-2.0
// Valid: echo types retain witnesses across a collapsing map.
//
// `constant` maps every input to 0, so distinct inputs share a base, yet
// their echoes keep distinct witnesses — structured loss, not erasure.

fn main() {
    let constant = |n: Int| 0

    let a: Echo[Int, Int] = echo(constant, 11)
    let b: Echo[Int, Int] = echo(constant, 22)

    // The map collapses both inputs to the same observed base.
    assert(echo_base(a) == 0)
    assert(echo_base(b) == 0)
    assert(echo_base(a) == echo_base(b))

    // But each echo retains its own witness.
    assert(echo_witness(a) == 11)
    assert(echo_witness(b) == 22)

    println("echo structured-loss: ok")
}
