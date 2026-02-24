// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional type assignment error
// Expected: Type error - cannot assign time to energy variable

fn test() {
    let energy: Resource<Energy> = 5s;  // Should fail: 5s is Time, not Energy
}
