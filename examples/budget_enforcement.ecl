// SPDX-License-Identifier: PMPL-1.0-or-later
// Resource budget enforcement with @requires constraints

// A function with strict energy budget
def efficient_sum(n: Int) -> Int
    @requires: energy < 10J
{
    // O(1) closed-form sum: n*(n+1)/2
    n * (n + 1) / 2
}

// An adaptive function with multiple solutions at different cost points
adaptive def compute(data: Array[Int]) -> Int
    @requires: energy < 100J
    @requires: carbon < 50gCO2e
    @optimize: minimize energy
{
    @solution "fast":
        @when: true
        @provides: energy: 5J, latency: 1ms, carbon: 2gCO2e
    {
        // Fast O(1) approximation
        len(data) * 42
    }

    @solution "accurate":
        @when: true
        @provides: energy: 50J, latency: 100ms, carbon: 20gCO2e
    {
        // Accurate computation
        let total = 0
        let i = 0
        while i < len(data) {
            total = total + data[i]
            i = i + 1
        }
        total
    }
}

def main() -> Unit {
    println("=== Budget Enforcement Demo ===")

    // Efficient sum with energy constraint
    let result = efficient_sum(100)
    println("Sum 1..100 =", result)

    // Adaptive computation selects cheapest solution
    let data = [1, 2, 3, 4, 5]
    let computed = compute(data)
    println("Computed result:", computed)

    println("")
    println("The runtime enforces resource budgets:")
    println("  energy < 100J, carbon < 50gCO2e")
    println("  Selected the 'fast' solution (5J vs 50J)")
}
