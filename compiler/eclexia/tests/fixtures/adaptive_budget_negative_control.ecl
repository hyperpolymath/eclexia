// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//
// Negative control for the ADR-001 Gate 0b exit test: the same two
// solutions as adaptive_budget_paired.ecl, but with the budget raised above
// both. An always-Disproved or always-Unknown verifier would fail this —
// both solutions must report Proved.

adaptive def compute(n: Int) -> Int
    @requires: energy < 300J
{
    @solution "fast":
        @when: true
        @provides: energy: 50J
    {
        n * 2
    }

    @solution "slow":
        @when: true
        @provides: energy: 200J
    {
        n + n
    }
}
