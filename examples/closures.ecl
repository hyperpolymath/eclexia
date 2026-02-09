// SPDX-License-Identifier: PMPL-1.0-or-later
// Closures and higher-order functions in Eclexia

fn apply(f: (Int) -> Int, x: Int) -> Int {
    f(x)
}

fn make_adder(n: Int) -> (Int) -> Int {
    |x| x + n
}

fn make_multiplier(n: Int) -> (Int) -> Int {
    |x| x * n
}

fn main() {
    println("=== Closures Demo ===")

    // Simple lambda
    let double = |x: Int| x * 2
    println("double(5) =", apply(double, 5))

    // Closure capturing environment
    let add5 = make_adder(5)
    let mul3 = make_multiplier(3)
    println("add5(10) =", apply(add5, 10))
    println("mul3(7) =", apply(mul3, 7))

    // Inline lambdas
    let result = apply(|x| x * x + 1, 4)
    println("|x| x*x+1 applied to 4 =", result)

    // Nested closures
    let add10 = make_adder(10)
    println("add10(add5(1)) =", apply(add10, apply(add5, 1)))
}
