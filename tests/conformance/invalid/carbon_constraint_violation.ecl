// SPDX-License-Identifier: AGPL-3.0-or-later
// Conformance test: carbon constraint violation
// Expected: FAIL with ResourceViolation (no solution within carbon budget)

adaptive def carbon_heavy_task(x: Int) -> Int
    @requires: carbon < 10gCO2e  // Strict carbon budget
    @optimize: minimize carbon
{
    // Only solution exceeds carbon budget
    @solution "polluting":
        @when: true
        @provides: energy: 10J, latency: 10ms, carbon: 500gCO2e
    {
        x * x
    }
}

def main() -> Unit {
    // This should fail: no solution provides carbon < 10gCO2e
    let result = carbon_heavy_task(10)
    println(result)
}
