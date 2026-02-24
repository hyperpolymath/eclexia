// SPDX-License-Identifier: PMPL-1.0-or-later
// Example: Higher-order functions
// Demonstrates passing functions as arguments and function composition.

fn apply(f: fn(Int) -> Int, x: Int) -> Int {
    f(x)
}

fn compose(f: fn(Int) -> Int, g: fn(Int) -> Int, x: Int) -> Int {
    f(g(x))
}

fn double(x: Int) -> Int {
    x * 2
}

fn square(x: Int) -> Int {
    x * x
}

fn increment(x: Int) -> Int {
    x + 1
}

fn negate(x: Int) -> Int {
    0 - x
}

fn main() {
    println("=== Higher-Order Functions Demo ===")

    // Passing named functions as arguments
    println("apply(double, 5) =", apply(double, 5))
    println("apply(square, 5) =", apply(square, 5))
    println("apply(increment, 5) =", apply(increment, 5))
    println("apply(negate, 5) =", apply(negate, 5))

    // Function composition
    println("")
    println("Function composition:")
    println("  double(square(3)) =", compose(double, square, 3))
    println("  square(double(3)) =", compose(square, double, 3))
    println("  increment(double(5)) =", compose(increment, double, 5))
    println("  negate(square(4)) =", compose(negate, square, 4))

    // Applying lambdas
    println("")
    println("Lambda expressions:")
    println("  apply(x -> x * 3, 7) =", apply(fn(x) -> x * 3, 7))
    println("  apply(x -> x + 100, 5) =", apply(fn(x) -> x + 100, 5))

    // Chained composition
    println("")
    println("Chained operations:")
    let result = compose(double, increment, 10)
    println("  double(increment(10)) =", result)
    let result2 = compose(increment, double, 10)
    println("  increment(double(10)) =", result2)
}
