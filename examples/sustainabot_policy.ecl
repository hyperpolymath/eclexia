// SPDX-License-Identifier: PMPL-1.0-or-later
// SustainaBot Policy — resource monitoring and enforcement rules.
//
// This policy evaluates resource usage against thresholds.
// When integrated via FFI, sustainabot passes resource metrics
// and receives a warn/ok decision.

// Check if energy usage exceeds threshold
fn check_energy(energy: Float, threshold: Float) -> Bool {
    energy > threshold
}

// Check if carbon exceeds threshold
fn check_carbon(carbon: Float, threshold: Float) -> Bool {
    carbon > threshold
}

// Evaluate a resource profile against policy thresholds
fn evaluate_policy(energy: Float, carbon: Float, memory: Int) -> Bool {
    // Warn if energy > 50J OR carbon > 5gCO2e OR memory > 10MB
    let energy_warn = check_energy(energy, 50.0);
    let carbon_warn = check_carbon(carbon, 5.0);
    let memory_warn = memory > 10000000;
    energy_warn || carbon_warn || memory_warn
}

// Adaptive policy evaluation: fast path for obvious cases
adaptive def should_warn(energy: Float, carbon: Float) -> Bool
    @requires: energy < 1J
    @requires: carbon < 0.001gCO2e
    @optimize: minimize energy
{
    @solution "trivial_ok":
        @when: true
        @provides: energy: 0.01J, latency: 0.1ms, carbon: 0.00001gCO2e
    {
        // Fast path: check if both are zero
        if energy == 0.0 {
            if carbon == 0.0 {
                false
            } else {
                carbon > 5.0
            }
        } else {
            energy > 50.0 || carbon > 5.0
        }
    }

    @solution "full_check":
        @when: true
        @provides: energy: 0.5J, latency: 2ms, carbon: 0.0005gCO2e
    {
        // Full evaluation with both thresholds
        check_energy(energy, 50.0) || check_carbon(carbon, 5.0)
    }
}

fn main() {
    println("=== SustainaBot Policy Demo ===");

    // Test normal resource usage
    println("");
    println("Test 1: Normal usage (energy=5.0, carbon=0.5)");
    let warn1 = evaluate_policy(5.0, 0.5, 1024);
    println("  Should warn:", warn1);

    // Test high energy usage
    println("");
    println("Test 2: High energy (energy=100.0, carbon=0.1)");
    let warn2 = evaluate_policy(100.0, 0.1, 512);
    println("  Should warn:", warn2);

    // Test high carbon usage
    println("");
    println("Test 3: High carbon (energy=1.0, carbon=10.0)");
    let warn3 = evaluate_policy(1.0, 10.0, 256);
    println("  Should warn:", warn3);

    // Test zero usage (fast path)
    println("");
    println("Test 4: Zero usage (energy=0.0, carbon=0.0)");
    let warn4 = should_warn(0.0, 0.0);
    println("  Should warn:", warn4);

    // Test adaptive dispatch
    println("");
    println("Test 5: Adaptive policy (energy=75.0, carbon=2.0)");
    let warn5 = should_warn(75.0, 2.0);
    println("  Should warn:", warn5);

    println("");
    println("Policy constraints:");
    println("  Warn if energy > 50J OR carbon > 5gCO2e");
    println("  Policy itself uses < 1J energy (dogfooding!)")
}
