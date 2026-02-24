// SPDX-License-Identifier: PMPL-1.0-or-later
// Conformance test: no solution satisfies constraints
// Expected: FAIL with ResourceViolation (no valid solution)

adaptive def impossible_task(n: Int) -> Int
    @requires: energy < 10J, latency < 5ms
    @optimize: minimize energy
{
    @solution "high_energy":
        @when: true
        @provides: energy: 100J, latency: 1ms  // Energy too high
    {
        n * 2
    }

    @solution "high_latency":
        @when: true
        @provides: energy: 5J, latency: 1000ms  // Latency too high
    {
        n + n
    }
}

def main() -> Unit
    @requires: energy < 10J, latency < 5ms
{
    // Neither solution satisfies both constraints
    let result = impossible_task(5)
    println(result)
}
