// SPDX-License-Identifier: AGPL-3.0-or-later
// Conformance test: adaptive function selects optimal solution
// Expected: Success, selects solution based on weighted cost

adaptive def process(n: Int) -> Int
    @requires: energy < 100J, latency < 500ms
    @optimize: minimize energy
{
    @solution "fast":
        @when: n > 10
        @provides: energy: 80J, latency: 50ms
    {
        n * 2
    }

    @solution "efficient":
        @when: true
        @provides: energy: 20J, latency: 200ms
    {
        n + n
    }
}

def main() -> Unit
    @requires: energy < 200J
{
    // Should select "efficient" solution (lower energy cost)
    let result = process(5)
    println(result)
}
