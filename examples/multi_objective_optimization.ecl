// SPDX-License-Identifier: PMPL-1.0-or-later
// Multi-objective optimization demo — energy, latency, carbon tradeoffs.

adaptive def render_frame(pixels: Int) -> Int
    @requires: energy < 200J
    @requires: latency < 50ms
    @requires: carbon < 100gCO2e
    @optimize: minimize carbon
{
    @solution "fast_gpu":
        @when: true
        @provides: energy: 80J, latency: 5ms, carbon: 20gCO2e
    {
        // Fastest, higher energy/carbon
        pixels * 2
    }

    @solution "eco_cpu":
        @when: true
        @provides: energy: 20J, latency: 40ms, carbon: 5gCO2e
    {
        // Low energy/carbon, higher latency
        pixels + 1
    }

    @solution "balanced":
        @when: true
        @provides: energy: 30J, latency: 15ms, carbon: 8gCO2e
    {
        // Balanced tradeoff
        pixels * 2 + 1
    }
}

fn main() {
    println("=== Multi-Objective Optimization Demo ===")

    let frame = render_frame(120)
    println("Rendered frame value:", frame)

    println("")
    println("Costs combine energy + latency + carbon for selection.")
    println("All solutions respect @requires constraints.")
}
