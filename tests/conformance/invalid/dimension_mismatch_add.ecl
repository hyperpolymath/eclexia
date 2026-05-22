// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional mismatch in addition
// Expected: Type error - cannot add energy and time

fn test() -> Resource<Energy> {
    let energy: Resource<Energy> = 100J;
    let time: Resource<Time> = 5s;

    // This should fail: cannot add different dimensions
    energy + time
}
