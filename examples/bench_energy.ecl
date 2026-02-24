// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//
// Energy benchmark examples for Eclexia.
//
// Run with: eclexia bench --energy
//
// These benchmarks measure both wall-clock time and energy consumption
// using RAPL (Running Average Power Limit) on Linux with Intel CPUs.
// Carbon cost is estimated using grid carbon intensity (default 400 gCO2e/kWh).

// === Compute-bound benchmarks ===

def fibonacci(n: Int) -> Int {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

def factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// === Benchmark functions ===

// Recursive fibonacci — high compute, low memory.
#[bench]
def bench_fib_recursive_15() -> Int {
    fibonacci(15)
}

// Factorial — moderate compute.
#[bench]
def bench_factorial_12() -> Int {
    factorial(12)
}

// Compare: recursive vs iterative fibonacci energy efficiency.
// Run both and compare joules/iteration in the output.
#[bench]
def bench_fib_recursive_20() -> Int {
    fibonacci(20)
}

fn main() {
    println("=== Energy Benchmark Demo (manual run) ===")
    println("fibonacci(15) =", fibonacci(15))
    println("factorial(12) =", factorial(12))
    println("Use `eclexia bench --energy` to run #[bench] functions.")
}
