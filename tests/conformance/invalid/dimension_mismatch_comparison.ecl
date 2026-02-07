// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional mismatch in comparison
// Expected: Type error - cannot compare energy and carbon

fn test() -> bool {
    let energy: Resource<Energy> = 100J;
    let carbon: Resource<Carbon> = 50gCO2;

    // This should fail: cannot compare different dimensions
    energy > carbon
}
