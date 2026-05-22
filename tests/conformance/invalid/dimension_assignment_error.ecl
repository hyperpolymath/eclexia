// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional type assignment error
// Expected: Type error - cannot assign time to energy variable

fn test() {
    let energy: Resource<Energy> = 5s;  // Should fail: 5s is Time, not Energy
}
