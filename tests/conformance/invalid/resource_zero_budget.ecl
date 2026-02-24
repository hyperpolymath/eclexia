// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Zero resource budget
// Expected: ResourceViolation - any operation exceeds zero budget

@requires(energy: 0J)
fn impossible() {
    let x = 42;  // Even this should fail with zero budget
}

fn main() {
    impossible();
}
