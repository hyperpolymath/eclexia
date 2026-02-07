// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Tracking multiple resource types simultaneously
// Expected: Success - energy, time, and carbon tracked independently

@requires(energy: 100J, time: 10ms, carbon: 20gCO2)
fn multi_resource() {
    // Uses some of each resource
    let x = compute();  // energy
    wait();             // time
    // carbon tracked automatically
}

fn compute() -> int {
    42
}

fn wait() {
    // Simulates waiting
}

fn main() {
    multi_resource();
}
