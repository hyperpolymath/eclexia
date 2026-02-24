// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Pattern matching with resource tracking
// Expected: Success

fn classify(x: int) -> string {
    match x {
        0 => "zero",
        1 => "one",
        _ => "other"
    }
}

fn main() {
    assert(classify(0) == "zero");
    assert(classify(5) == "other");
}
