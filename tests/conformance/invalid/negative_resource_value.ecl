// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Negative resource value
// Expected: Type error - resources cannot be negative

fn main() {
    let energy: Resource<Energy> = -100J;  // Should fail
}
