// SPDX-License-Identifier: PMPL-1.0-or-later
// Shadow price optimization demo — uses @when + shadow_price to gate solutions.

adaptive def choose_strategy(n: Int) -> Int
    @requires: energy < 200J
    @requires: carbon < 10gCO2e
    @optimize: minimize energy
{
    @solution "energy_saver":
        @when: shadow_price("energy") > 0.5
        @provides: energy: 5J, latency: 10ms, carbon: 0.5gCO2e
    {
        // Low energy path
        n * n
    }

    @solution "fast_path":
        @when: shadow_price("energy") <= 0.5
        @provides: energy: 20J, latency: 1ms, carbon: 1gCO2e
    {
        // Faster but higher energy
        n * n + n
    }

    @solution "balanced":
        @when: true
        @provides: energy: 10J, latency: 5ms, carbon: 0.8gCO2e
    {
        n * (n + 1)
    }
}

fn main() {
    println("=== Shadow Price Optimization Demo ===")

    let energy_price = shadow_price("energy")
    let carbon_price = shadow_price("carbon")
    println("Current shadow prices:")
    println("  energy:", energy_price)
    println("  carbon:", carbon_price)

    println("")
    println("Choosing strategy for n = 7:")
    let result = choose_strategy(7)
    println("  result =", result)

    println("")
    println("Selection is gated by @when + shadow_price, then minimized by cost.")
}
