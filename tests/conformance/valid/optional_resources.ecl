// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Optional resource annotations
// Expected: Success - functions without @requires work

fn no_annotation() -> int {
    42
}

fn main() {
    let result = no_annotation();
    assert(result == 42);
}
