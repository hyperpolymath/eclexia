// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//
// ADR-001 Gate 0b exit test: a paired over-limit / under-limit fixture.
// `slow` provides more energy than the budget allows (Disproved); `fast`
// provides less (Proved). Neither an always-Proved nor an always-Unknown
// verifier can pass this fixture.

adaptive def compute(n: Int) -> Int
    @requires: energy < 100J
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
