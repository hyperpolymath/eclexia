// SPDX-License-Identifier: MPL-2.0
// Echo + Landauer: information loss, priced into the resource economy.
//
// Eclexia prices what you give up (shadow prices). An echo is what you give
// up, retained. The bridge is thermodynamic: irreversibly erasing an echo's
// witness costs energy by Landauer's principle (E = k_B * T * ln N), and that
// is exactly the Resource[Energy] the language tracks. Keeping the echo is
// reversible (Bennett): zero cost. See formal/coq/src/EchoThermo.v.

fn main() {
    println("=== Echo + Landauer: pricing structured loss ===")

    // `collapse` sends every input to the same output: 8 distinct states
    // would land on one base, losing 3 bits (log2 8).
    let collapse = |n: Int| 0
    let e = echo(collapse, 5)

    // Reversible: the echo retains its witness, so nothing is erased.
    let free: Resource[Energy] = landauer_cost(1, 300.0)
    println("reversible (echo kept) @300K:", free)

    // Irreversible: erasing a fibre of 8 states costs Landauer energy.
    let cost: Resource[Energy] = landauer_cost(8, 300.0)
    println("erase 8 states @300K:", cost)

    // ...but the input is still recoverable from the echo: reversible
    // representation of an otherwise irreversible computation.
    println("recovered witness:", echo_witness(e))
    println("observed base:", echo_base(e))
}
