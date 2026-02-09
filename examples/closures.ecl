// SPDX-License-Identifier: PMPL-1.0-or-later
// Closures and higher-order functions in Eclexia

def apply(f: (Int) -> Int, x: Int) -> Int {
    f(x)
}

def compose(f: (Int) -> Int, g: (Int) -> Int) -> (Int) -> Int {
    |x| f(g(x))
}

def make_adder(n: Int) -> (Int) -> Int {
    |x| x + n
}

def make_multiplier(n: Int) -> (Int) -> Int {
    |x| x * n
}

def main() -> Unit {
    println("=== Closures Demo ===")

    // Simple lambda
    let double = |x: Int| x * 2
    println("double(5) =", apply(double, 5))

    // Closure capturing environment
    let add5 = make_adder(5)
    let mul3 = make_multiplier(3)
    println("add5(10) =", apply(add5, 10))
    println("mul3(7) =", apply(mul3, 7))

    // Function composition
    let add5_then_mul3 = compose(mul3, add5)
    println("(5 + 5) * 3 =", apply(add5_then_mul3, 5))

    // Inline lambdas
    let result = apply(|x| x * x + 1, 4)
    println("|x| x*x+1 applied to 4 =", result)
}
