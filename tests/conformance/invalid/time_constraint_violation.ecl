// SPDX-License-Identifier: PMPL-1.0-or-later
// Conformance test: time/latency constraint violation
// Expected: FAIL with ResourceViolation (no solution within latency budget)

adaptive def slow_task(n: Int) -> Int
    @requires: latency < 10ms  // Very tight latency budget
    @optimize: minimize latency
{
    // Only solution exceeds the latency budget
    @solution "slow":
        @when: true
        @provides: energy: 5J, latency: 5000ms
    {
        n * n
    }
}

def main() -> Unit {
    // This should fail: no solution provides latency < 10ms
    let result = slow_task(42)
    println(result)
}
