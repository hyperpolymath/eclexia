// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Adaptive block with three solutions
// Expected: Success - selects based on weighted cost

adaptive fn process(data: int) -> int {
    fastest @requires(energy: 200J, time: 1ms, carbon: 50gCO2) {
        data + 1
    }

    balanced @requires(energy: 50J, time: 5ms, carbon: 10gCO2) {
        data + 1
    }

    greenest @requires(energy: 10J, time: 20ms, carbon: 1gCO2) {
        data + 1
    }
}

fn main() {
    let result = process(100);
    assert(result == 101);
}
