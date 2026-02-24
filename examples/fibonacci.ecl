// SPDX-License-Identifier: PMPL-1.0-or-later
// Fibonacci — recursive implementation.

fn fib(n: Int) -> Int {
    if n <= 1 {
        n
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn fib_tail(n: Int, a: Int, b: Int) -> Int {
    if n <= 0 {
        a
    } else {
        fib_tail(n - 1, b, a + b)
    }
}

fn main() {
    println("=== Fibonacci ===");
    println("Recursive:");
    println("  fib(0) =", fib(0));
    println("  fib(1) =", fib(1));
    println("  fib(5) =", fib(5));
    println("  fib(10) =", fib(10));

    println("");
    println("Tail-recursive:");
    println("  fib_tail(0) =", fib_tail(0, 0, 1));
    println("  fib_tail(1) =", fib_tail(1, 0, 1));
    println("  fib_tail(5) =", fib_tail(5, 0, 1));
    println("  fib_tail(10) =", fib_tail(10, 0, 1));
    println("  fib_tail(20) =", fib_tail(20, 0, 1))
}
