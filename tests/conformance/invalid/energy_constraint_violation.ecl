// SPDX-License-Identifier: PMPL-1.0-or-later
// Conformance test: energy constraint violation
// Expected: FAIL with ResourceViolation (no solution within budget)

adaptive def expensive_task(x: Int) -> Int
    @requires: energy < 10J  // Very tight energy budget
    @optimize: minimize energy
{
    // Only solution exceeds the energy budget
    @solution "heavy":
        @when: true
        @provides: energy: 500J, latency: 10ms
    {
        x * x * x * x
    }
}

def main() -> Unit {
    // This should fail: no solution provides energy < 10J
    let result = expensive_task(10)
    println(result)
}
