// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Comparison of same-dimension resources, and comparison of a
// dimensionless ratio (Resource / Resource with matching dimensions)
// against a bare literal.
// Expected: Success - dimensional agreement checking (ADR-001 section
// 2.2.2) must not over-fire on these two legitimate cases.

fn test() -> bool {
    let e1: Resource<Energy> = 100J;
    let e2: Resource<Energy> = 50J;

    // Resource<Energy> vs Resource<Energy>: same dimension, allowed.
    let same_dimension = e1 > e2;

    // Resource<Energy> / Resource<Energy> yields a dimensionless ratio,
    // which may be compared against a bare (dimensionless) literal.
    let ratio = e1 / e2;
    let ratio_check = ratio > 0.5;

    same_dimension && ratio_check
}
