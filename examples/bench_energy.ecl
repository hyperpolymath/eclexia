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

def fibonacci_iterative(n: Int) -> Int {
    let a = 0
    let b = 1
    let i = 0
    while i < n {
        let temp = b
        b = a + b
        a = temp
        i = i + 1
    }
    a
}

def factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// === Memory-bound benchmarks ===

def build_list(n: Int) -> List<Int> {
    let result = []
    let i = 0
    while i < n {
        result = result ++ [i]
        i = i + 1
    }
    result
}

def sum_list(xs: List<Int>) -> Int {
    match xs {
        [] => 0,
        [h, ..t] => h + sum_list(t),
    }
}

// === Benchmark functions ===

/// Recursive fibonacci — high compute, low memory.
#[bench]
def bench_fib_recursive_15() -> Int {
    fibonacci(15)
}

/// Iterative fibonacci — lower compute, minimal memory.
#[bench]
def bench_fib_iterative_15() -> Int {
    fibonacci_iterative(15)
}

/// Factorial — moderate compute.
#[bench]
def bench_factorial_12() -> Int {
    factorial(12)
}

/// List construction — memory allocation heavy.
#[bench]
def bench_build_list_50() -> List<Int> {
    build_list(50)
}

/// List summation — memory traversal.
#[bench]
def bench_sum_list_50() -> Int {
    sum_list(build_list(50))
}

/// Compare: recursive vs iterative fibonacci energy efficiency.
/// Run both and compare joules/iteration in the output.
#[bench]
def bench_fib_recursive_20() -> Int {
    fibonacci(20)
}

#[bench]
def bench_fib_iterative_1000() -> Int {
    fibonacci_iterative(1000)
}
