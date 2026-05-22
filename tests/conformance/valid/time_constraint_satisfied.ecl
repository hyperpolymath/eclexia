// SPDX-License-Identifier: MPL-2.0
// Conformance test: time/latency constraint within budget
// Expected: Success, completes within latency bound

def quick_operation(n: Int) -> Int
    @requires: latency < 100ms
{
    n + 1
}

def main() -> Unit
    @requires: latency < 500ms
{
    let x = quick_operation(5)
    let y = quick_operation(x)
    println(y)
}
