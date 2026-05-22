// SPDX-License-Identifier: MPL-2.0
// Conformance test: basic resource-typed function
// Expected: Success, outputs "Hello, Resources!"

def main() -> Unit
    @requires: energy < 1J
{
    println("Hello, Resources!")
}
