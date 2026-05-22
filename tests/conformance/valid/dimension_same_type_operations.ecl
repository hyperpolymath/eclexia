// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Operations on same dimensional type
// Expected: Success - can add/subtract same dimensions

fn test() -> Resource<Energy> {
    let e1: Resource<Energy> = 100J;
    let e2: Resource<Energy> = 50J;

    let total = e1 + e2;     // 150J
    let diff = total - e2;   // 100J

    diff
}
