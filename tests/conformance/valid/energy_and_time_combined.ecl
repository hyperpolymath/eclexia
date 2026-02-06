// SPDX-License-Identifier: AGPL-3.0-or-later
// Conformance test: combined energy + time constraints
// Expected: Success, both resource types tracked correctly

def work(x: Int) -> Int
    @requires: energy < 50J, latency < 100ms
{
    x * x
}

def main() -> Unit
    @requires: energy < 100J, latency < 300ms
{
    let a = work(3)
    let b = work(4)
    println(a + b)
}
