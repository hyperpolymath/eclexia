// SPDX-License-Identifier: AGPL-3.0-or-later
// Conformance test: energy constraint within budget
// Expected: Success, returns computed value

def compute(x: Int) -> Int
    @requires: energy < 100J
{
    x * x + x
}

def main() -> Unit
    @requires: energy < 200J
{
    let result = compute(10)
    println(result)
}
