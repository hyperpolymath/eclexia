// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Negative resource value
// Expected: Type error - resources cannot be negative

fn main() {
    let energy: Resource<Energy> = -100J;  // Should fail
}
