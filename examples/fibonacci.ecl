// SPDX-License-Identifier: MIT
// Adaptive Fibonacci implementation - demonstrates solution selection

// Helper function for tail-recursive fibonacci
def fib_helper(n: Int, a: Int, b: Int) -> Int {
    if n <= 0 {
        a
    } else {
        fib_helper(n - 1, b, a + b)
    }
}

// Efficient tail-recursive fibonacci
def efficient_fib(n: Int) -> Int {
    fib_helper(n, 0, 1)
}

// Simple fibonacci using the naive recursive algorithm
def simple_fib(n: Int) -> Int {
    if n <= 1 {
        n
    } else {
        simple_fib(n - 1) + simple_fib(n - 2)
    }
}

// Adaptive fibonacci: runtime selects best solution based on constraints
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    // Tail-recursive is more efficient (lower energy cost)
    @solution "efficient":
        @when: true
        @provides: energy: 5J, latency: 10ms, carbon: 1gCO2e
    {
        efficient_fib(n)
    }

    // Naive recursive uses more energy
    @solution "naive":
        @when: true
        @provides: energy: 50J, latency: 50ms, carbon: 5gCO2e
    {
        simple_fib(n)
    }
}

def main() -> Unit {
    println("Eclexia Adaptive Fibonacci Demo")
    println("================================")

    // Call the adaptive fibonacci function
    let result = fibonacci(10)

    println("")
    println("fibonacci(10) =", result)
    println("")
    println("The runtime selected the best solution based on shadow prices:")
    println("  efficient: cost = 5 + 10 + 1 = 16")
    println("  naive:     cost = 50 + 50 + 5 = 105")
}
