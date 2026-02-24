// SPDX-License-Identifier: PMPL-1.0-or-later
// Opportunity stress-test: adaptive budgeting, shadow prices, collections

adaptive def ledger_analytics(values: [Float], categories: [String]) -> Result<Float, String>
    @requires: energy < 200J, carbon < 5gCO2e
    @optimize: minimize carbon
{
    @solution "fast_path":
        @when: true
        @provides: energy: 50J, carbon: 0.8gCO2e
    {
        let mut sum = 0.0
        for value in values {
            sum = sum + value
        }
        Ok(sum / (len(values) as Float))
    }

    @solution "green_path":
        @when: true
        @provides: energy: 80J, carbon: 0.4gCO2e
    {
        let mut research_total = 0.0
        let mut research_count = 0
        for idx in range(0, len(categories)) {
            if categories[idx] == "research" {
                research_total = research_total + values[idx]
                research_count = research_count + 1
            }
        }
        if research_count == 0 {
            Err("no research entries available".to_string())
        } else {
            Ok(research_total / (research_count as Float))
        }
    }

    @solution "realtime_path":
        @when: true
        @provides: energy: 100J, carbon: 1gCO2e
    {
        let mut research_count = 0
        let mut operations_count = 0
        let mut finance_count = 0
        for idx in range(0, len(categories)) {
            let category = categories[idx]
            if category == "research" {
                research_count = research_count + 1
            } else {
                if category == "operations" {
                    operations_count = operations_count + 1
                } else {
                    if category == "finance" {
                        finance_count = finance_count + 1
                    }
                }
            }
        }
        println("Category tallies:", research_count, operations_count, finance_count)
        Err("realtime insights deferred".to_string())
    }
}

fn main() {
    println("=== Comprehensive Opportunity Demo ===")

    let values = [42.0, 58.0, 15.5, 33.3, 81.7]
    let categories = ["research", "operations", "research", "finance", "operations"]

    match ledger_analytics(values, categories) {
        Ok(avg) => println("Adaptive insight:", avg),
        Err(e) => println("Adaptive fallback:", e),
    }

    println("Vector length:", len(values))
    println("Budget guardrails enforce energy & carbon limits.")
    println("Switch paths when carbon pricing rises.")
}
