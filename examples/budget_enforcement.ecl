// SPDX-License-Identifier: PMPL-1.0-or-later
// Resource budget enforcement with @requires constraints

// A function with strict energy budget
def efficient_sum(n: Int) -> Int
    @requires: energy < 10J
{
    // O(1) closed-form sum: n*(n+1)/2
    n * (n + 1) / 2
}

// Adaptive function with multiple cost-optimal solutions
adaptive def compute(n: Int) -> Int
    @requires: energy < 100J
    @requires: carbon < 50gCO2e
    @optimize: minimize energy
{
    @solution "fast":
        @when: true
        @provides: energy: 5J, latency: 1ms, carbon: 2gCO2e
    {
        n * 42
    }

    @solution "accurate":
        @when: true
        @provides: energy: 50J, latency: 100ms, carbon: 20gCO2e
    {
        // Use accumulator pattern (no let inside while in parametered fn)
        n * (n - 1) / 2
    }
}

fn main() {
    println("=== Budget Enforcement Demo ===")

    // Efficient sum with energy constraint
    let result = efficient_sum(100)
    println("Sum 1..100 =", result)

    // Adaptive computation selects cheapest solution
    let computed = compute(5)
    println("Computed result:", computed)

    println("")
    println("The runtime enforces resource budgets:")
    println("  energy < 100J, carbon < 50gCO2e")
    println("  Selected the cheapest viable solution")
}
