// SPDX-License-Identifier: MPL-2.0
// Valid: Echo's structured loss priced via Landauer; the type checker
// accepts landauer_cost(...) as a Resource[Energy], and a retained echo
// witness is recoverable (reversible representation).

fn main() {
    let collapse = |n: Int| 0
    let e: Echo[Int, Int] = echo(collapse, 5)

    // Reversible retention costs nothing; collapsing a fibre costs energy.
    let _free: Resource[Energy] = landauer_cost(1, 300.0)
    let _cost: Resource[Energy] = landauer_cost(8, 300.0)

    // The witness survives in the echo.
    assert(echo_witness(e) == 5)
    assert(echo_base(e) == 0)

    println("echo + landauer: ok")
}
