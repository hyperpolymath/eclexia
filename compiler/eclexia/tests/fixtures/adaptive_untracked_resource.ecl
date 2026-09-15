// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//
// ADR-001 section 1, T4 (per-resource coverage): `carbon` is constrained but
// no solution declares a `@provides` for it. The verifier must report
// `Unknown` for carbon specifically, not silently treat absent evidence as
// zero usage (which would falsely Prove it) and not let the tracked
// `energy` resource's evidence bleed into the untracked one.

adaptive def compute(n: Int) -> Int
    @requires: energy < 100J
    @requires: carbon < 50gCO2e
{
    @solution "only":
        @when: true
        @provides: energy: 50J
    {
        n * 2
    }
}
