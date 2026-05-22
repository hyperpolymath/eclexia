// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional mismatch in comparison
// Expected: Type error - cannot compare energy and carbon

fn test() -> bool {
    let energy: Resource<Energy> = 100J;
    let carbon: Resource<Carbon> = 50gCO2;

    // This should fail: cannot compare different dimensions
    energy > carbon
}
