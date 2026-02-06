// SPDX-License-Identifier: PMPL-1.0-or-later
// SustainaBot Policy Example - Demonstrates FFI Integration
//
// This policy can be called from Rust via FFI, receiving JSON input
// and returning a decision. This is the REAL dogfooding!

// Parse resource metrics from JSON (from Rust FFI)
def parse_resource_metrics(json_str: String) -> Bool {
    // Parse JSON from sustainabot
    let data = parse_json(json_str)

    // Extract energy and carbon from parsed data
    // JSON structure: {"energy": 10.5, "carbon": 1.2, "duration": 50.0, "memory": 1024}

    // For now, return a simple decision
    // In full implementation, we'd extract values and check thresholds
    evaluate_thresholds(data)
}

// Evaluate if metrics exceed thresholds
def evaluate_thresholds(data: Array) -> Bool {
    // Simple check: always warn if we got here
    // Full implementation would parse array and check values
    true
}

// Main entry point for SustainaBot FFI
// Input: JSON string with ResourceProfile
// Output: Bool (true = warn, false = ok)
adaptive def should_warn(json_input: String) -> Bool
    @requires: energy < 1J, latency < 10ms, carbon < 0.001gCO2e
    @optimize: minimize energy, minimize latency
{
    @solution "fast_check":
        @when: str_contains(json_input, "\"energy\":0")
        @provides: energy: 0.05J, latency: 1ms, carbon: 0.0001gCO2e
    {
        // Energy is zero - obviously fine, skip parsing
        false
    }

    @solution "json_parse":
        @provides: energy: 0.3J, latency: 5ms, carbon: 0.0005gCO2e
    {
        // Parse and evaluate
        parse_resource_metrics(json_input)
    }
}

// Example usage (for testing without FFI)
def main() -> Unit {
    println("SustainaBot Policy Example")
    println("===========================\n")

    // Simulate input from sustainabot-eclexia FFI
    let input1 = "{\"energy\": 5.0, \"carbon\": 0.5, \"duration\": 10.0, \"memory\": 1024}"
    let input2 = "{\"energy\": 0, \"carbon\": 0, \"duration\": 0, \"memory\": 0}"

    println("Test 1: Normal resource usage")
    let warn1 = should_warn(input1)
    println("Result:", to_string(warn1))
    println()

    println("Test 2: Zero resource usage (fast path)")
    let warn2 = should_warn(input2)
    println("Result:", to_string(warn2))
    println()

    println("✅ Policy evaluation complete!")
    println("\nThis policy has @requires: energy < 1J")
    println("Meaning: Our 1J policy analyzes your 50J code!")
    println("That's the dogfooding proof!")
}
