// SPDX-License-Identifier: MIT
// Example benchmark file demonstrating the benchmarking framework

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

def sum_range(n: Int) -> Int {
    if n <= 0 {
        0
    } else {
        n + sum_range(n - 1)
    }
}

#[bench]
def bench_fibonacci_10() -> Int {
    fibonacci(10)
}

#[bench]
def bench_factorial_10() -> Int {
    factorial(10)
}

#[bench]
def bench_sum_100() -> Int {
    sum_range(100)
}

#[bench]
#[ignore]
def bench_slow_operation() -> Int {
    // This benchmark is ignored as it's too slow
    fibonacci(20)
}
