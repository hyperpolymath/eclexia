// SPDX-License-Identifier: MPL-2.0
// Echo types: structured loss as a first-class type.
//
// An echo of a map `f : A -> B` at an input `x` is the value `echo(f, x)`
// of type `Echo[A, B]`. It pairs the *retained witness* `x` with the
// *observed base* `f x`. When `f` collapses several inputs to the same
// output, their echoes share a base but keep distinct witnesses — loss
// that is not total erasure. (See THEORY.md §5.5: Echo is a graded
// comonad of structured loss; `echo_base` is the counit.)

fn main() {
    println("=== Echo Types: loss that is not erasure ===")

    // `sign` collapses every non-negative input to 1.
    let sign = |n: Int| if n >= 0 { 1 } else { 0 }

    // Two distinct inputs the function cannot tell apart.
    let e3: Echo[Int, Int] = echo(sign, 3)
    let e7: Echo[Int, Int] = echo(sign, 7)

    // The observed bases agree: `f` lost the distinction.
    println("base(echo(sign, 3)) =", echo_base(e3))
    println("base(echo(sign, 7)) =", echo_base(e7))

    // But each echo still carries its own witness: the loss is recoverable.
    println("witness(echo(sign, 3)) =", echo_witness(e3))
    println("witness(echo(sign, 7)) =", echo_witness(e7))

    // A negative input lands in the other fibre.
    let em: Echo[Int, Int] = echo(sign, -4)
    println("base(echo(sign, -4)) =", echo_base(em))
    println("witness(echo(sign, -4)) =", echo_witness(em))
}
