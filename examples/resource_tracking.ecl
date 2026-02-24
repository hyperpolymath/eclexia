// SPDX-License-Identifier: PMPL-1.0-or-later
// Resource tracking demo — shows @requires budgets and shadow prices.

// Cheap computation with tight energy budget
// (Runtime enforces declared budgets across calls)
def cheap_compute(n: Int) -> Int
    @requires: energy < 5J
{
    n + 1
}

// Moderate computation with both energy and carbon budgets
def moderate_compute(n: Int) -> Int
    @requires: energy < 40J
    @requires: carbon < 2gCO2e
{
    n * n + 1
}

// Combined computation (nested resource usage)
def combined_compute(n: Int) -> Int
    @requires: energy < 100J
    @requires: carbon < 5gCO2e
{
    cheap_compute(n) + moderate_compute(n)
}

fn main() {
    println("=== Resource Tracking Demo ===")

    let a = cheap_compute(10)
    let b = moderate_compute(5)
    let c = combined_compute(3)

    println("cheap_compute(10) =", a)
    println("moderate_compute(5) =", b)
    println("combined_compute(3) =", c)

    println("")
    println("Shadow prices:")
    println("  energy:", shadow_price("energy"))
    println("  carbon:", shadow_price("carbon"))

    println("")
    println("Budgets enforced via @requires on each function.")
}
