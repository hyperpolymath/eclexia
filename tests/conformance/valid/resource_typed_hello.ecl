// SPDX-License-Identifier: AGPL-3.0-or-later
// Conformance test: basic resource-typed function
// Expected: Success, outputs "Hello, Resources!"

def main() -> Unit
    @requires: energy < 1J
{
    println("Hello, Resources!")
}
