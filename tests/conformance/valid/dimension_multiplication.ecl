// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional analysis with multiplication
// Expected: Success - multiplying dimensioned values produces correct result dimension

fn test() -> Resource<Energy> {
    let power: f64 = 10.0;  // Watts
    let time: f64 = 5.0;     // Seconds

    // Power * Time = Energy
    let energy = power * time;  // Should be 50 Joules

    energy as Resource<Energy>
}
