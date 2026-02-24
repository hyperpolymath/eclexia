// SPDX-License-Identifier: PMPL-1.0-or-later
// Conformance test: impossible combined constraints
// Expected: FAIL with ResourceViolation (cannot satisfy both energy and latency)

adaptive def conflicting_task(x: Int) -> Int
    @requires: energy < 10J, latency < 10ms  // Impossible combination
    @optimize: minimize energy
{
    // Low energy but high latency
    @solution "low_energy":
        @when: true
        @provides: energy: 5J, latency: 1000ms
    {
        x + 1
    }

    // Low latency but high energy
    @solution "low_latency":
        @when: true
        @provides: energy: 500J, latency: 5ms
    {
        x * 2
    }
}

def main() -> Unit {
    // Neither solution satisfies both constraints
    let result = conflicting_task(5)
    println(result)
}
