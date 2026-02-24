// SPDX-License-Identifier: PMPL-1.0-or-later
// Carbon-aware computation — demonstrates resource-constrained scheduling.
//
// Eclexia's economics-as-code model lets functions declare carbon budgets.
// The runtime selects the cheapest viable solution at dispatch time.

type Dataset = { size: Int, name: String }

// A low-carbon data processing function
def process_data(data: Dataset) -> Int
    @requires: energy < 50J
    @requires: carbon < 10gCO2e
{
    // O(1) summary statistic — stays within energy budget
    data.size * 42
}

// Adaptive function: runtime picks the greenest viable solution
adaptive def analyze(n: Int) -> Int
    @requires: energy < 200J
    @requires: carbon < 100gCO2e
    @optimize: minimize carbon
{
    @solution "lightweight":
        @when: true
        @provides: energy: 10J, latency: 5ms, carbon: 1gCO2e
    {
        // Simple heuristic — very low carbon
        n * 2 + 1
    }

    @solution "thorough":
        @when: true
        @provides: energy: 150J, latency: 500ms, carbon: 50gCO2e
    {
        // More accurate but higher carbon cost
        n * n + n + 1
    }
}

fn main() {
    println("=== Carbon-Aware Computing ===");

    let data = Dataset { size: 1000, name: "sensor_readings" };
    println("Processing dataset:", data.name);
    let result = process_data(data);
    println("Result:", result);

    println("");
    println("Adaptive analysis (minimize carbon):");
    let analysis = analyze(10);
    println("  analyze(10) =", analysis);

    let analysis2 = analyze(100);
    println("  analyze(100) =", analysis2);

    println("");
    println("The runtime enforces:");
    println("  energy < 200J, carbon < 100gCO2e");
    println("  Selected the lowest-carbon viable solution")
}
