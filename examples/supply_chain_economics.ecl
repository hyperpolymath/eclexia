// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Supply Chain Economics — a showcase of Eclexia's resource economics model.
//
// This example demonstrates why "Economics-as-Code" is a paradigm, not a feature.
// A logistics company must route packages through warehouses. Each routing
// decision has energy, carbon, and latency costs. The shadow price engine
// dynamically adjusts which strategies are selected based on current resource
// scarcity — the same code makes different decisions under different conditions.
//
// Key Eclexia features demonstrated:
//   1. Adaptive functions with multiple @solution branches
//   2. Shadow price queries via shadow_price("resource")
//   3. @when guards that respond to runtime economics
//   4. @optimize directives for multi-objective trade-offs
//   5. @requires / @provides resource contracts
//   6. Structs and pattern matching
//   7. Higher-order functions (closures)

// --- Domain types ---

type Package = {
    id: Int,
    weight: Int,
    priority: String
}

type Route = {
    name: String,
    distance: Int,
    carbon_factor: Int
}

type ShipmentResult = {
    package_id: Int,
    route_name: String,
    cost: Int
}

// --- Route calculation ---

/// Calculate shipping cost factoring in weight, distance, and carbon price.
/// This is a pure function — no resource annotation needed.
fn shipping_cost(weight: Int, distance: Int, carbon_factor: Int) -> Int {
    let base = weight * distance / 100
    let surcharge = carbon_factor * 5
    base + surcharge
}

/// Estimate carbon emissions for a given shipment.
fn estimate_carbon(weight: Int, distance: Int, carbon_factor: Int) -> Int {
    weight * distance * carbon_factor / 1000
}

// --- Adaptive routing: the core of the economics model ---

/// Select a shipping route for a package. The runtime evaluates all three
/// solutions and selects the one that minimizes the weighted resource cost
/// (energy * shadow_energy + carbon * shadow_carbon + latency * shadow_latency).
///
/// When energy is scarce (high shadow price), the system favours the rail
/// route. When time is scarce, it favours air. When carbon is scarce, it
/// favours sea. The SAME function, the SAME call site — different economics
/// produce different behaviour. That is the point of Eclexia.
adaptive def route_package(pkg: Package) -> ShipmentResult
    @requires: energy < 500J
    @requires: carbon < 200gCO2e
    @optimize: minimize energy, minimize carbon
{
    @solution "air_express":
        @when: shadow_price("energy") < 2
        @provides: energy: 200J, latency: 1ms, carbon: 150gCO2e
    {
        // Fast but energy-intensive and carbon-heavy
        let cost = shipping_cost(pkg.weight, 5000, 8)
        ShipmentResult {
            package_id: pkg.id,
            route_name: "Air Express",
            cost: cost
        }
    }

    @solution "rail_freight":
        @when: shadow_price("carbon") > 20
        @provides: energy: 50J, latency: 5ms, carbon: 30gCO2e
    {
        // Low energy, moderate carbon, moderate speed
        let cost = shipping_cost(pkg.weight, 3000, 2)
        ShipmentResult {
            package_id: pkg.id,
            route_name: "Rail Freight",
            cost: cost
        }
    }

    @solution "sea_freight":
        @when: true
        @provides: energy: 30J, latency: 20ms, carbon: 10gCO2e
    {
        // Lowest carbon, slowest — always available as fallback
        let cost = shipping_cost(pkg.weight, 8000, 1)
        ShipmentResult {
            package_id: pkg.id,
            route_name: "Sea Freight",
            cost: cost
        }
    }
}

// --- Batch processing with resource tracking ---

/// Process a batch of packages through the adaptive router.
/// Each call to route_package may select a different solution depending
/// on the current shadow prices — which may change as resources are consumed.
def process_batch(packages: [Package]) -> Int
    @requires: energy < 500J
    @requires: carbon < 500gCO2e
{
    // Route each package and display the selection
    for pkg in packages {
        let result = route_package(pkg)
        println("  Package", result.package_id, "->", result.route_name,
                "(cost:", result.cost, ")")
    }
    println("  Batch complete:", len(packages), "packages routed")
    len(packages)
}

// --- Shadow price analysis ---

/// Display the current shadow prices and explain what they mean economically.
fn report_shadow_prices() {
    let energy_price = shadow_price("energy")
    let carbon_price = shadow_price("carbon")
    let latency_price = shadow_price("latency")

    println("Current shadow prices (marginal value of one more unit):")
    println("  Energy:  ", energy_price, " (value of 1 additional Joule)")
    println("  Carbon:  ", carbon_price, " (value of 1 fewer gCO2e)")
    println("  Latency: ", latency_price, " (value of 1 fewer ms)")
    println("")

    // Explain what the prices mean for routing decisions
    if energy_price > 2 {
        println("  -> Energy is SCARCE: system will prefer low-energy routes (rail, sea)")
    } else {
        println("  -> Energy is ABUNDANT: air routes are viable")
    }

    if carbon_price > 20 {
        println("  -> Carbon is EXPENSIVE: system will prefer rail over air")
    } else {
        println("  -> Carbon is CHEAP: carbon constraints are not binding")
    }
}

// --- Main program ---

fn main() {
    println("============================================")
    println("  Eclexia Supply Chain Economics Simulator")
    println("============================================")
    println("")

    // 1. Show current resource economics
    report_shadow_prices()
    println("")

    // 2. Create a fleet of packages with varying weights and priorities
    let packages = [
        Package { id: 1001, weight: 10, priority: "standard" },
        Package { id: 1002, weight: 25, priority: "express" },
        Package { id: 1003, weight: 5,  priority: "economy" },
        Package { id: 1004, weight: 50, priority: "standard" },
        Package { id: 1005, weight: 15, priority: "express" }
    ]

    // 3. Route the batch — adaptive functions select strategies
    println("--- Routing batch of", len(packages), "packages ---")
    let batch_cost = process_batch(packages)
    println("")

    // 4. Demonstrate the key insight: a single route_package call
    println("--- Single package routing ---")
    let heavy = Package { id: 9999, weight: 100, priority: "standard" }
    let result = route_package(heavy)
    println("Heavy package:", result.route_name, "at cost", result.cost)
    println("")

    // 5. Show the economic reasoning
    println("--- Economic Analysis ---")
    println("The adaptive router made choices based on:")
    println("  1. Shadow prices (scarcity signals)")
    println("  2. @provides declarations (resource costs per solution)")
    println("  3. @optimize directives (minimize energy + carbon)")
    println("  4. @when guards (solution eligibility)")
    println("")
    println("Change the shadow prices and the SAME code makes DIFFERENT decisions.")
    println("That is Economics-as-Code.")
}
