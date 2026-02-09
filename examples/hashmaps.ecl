// SPDX-License-Identifier: PMPL-1.0-or-later
// Example: HashMap operations
// Demonstrates creating and manipulating hash maps with builtin functions.

fn main() {
    println("=== HashMap Demo ===")

    // Create a new hashmap
    let scores = hashmap_new()

    // Insert key-value pairs (mutates in place, returns Unit)
    hashmap_insert(scores, "Alice", 95)
    hashmap_insert(scores, "Bob", 87)
    hashmap_insert(scores, "Charlie", 92)
    hashmap_insert(scores, "Diana", 88)

    // Check size
    println("Number of students:", hashmap_len(scores))

    // Look up values
    println("")
    println("Scores:")
    println("  Alice:", hashmap_get(scores, "Alice"))
    println("  Bob:", hashmap_get(scores, "Bob"))
    println("  Charlie:", hashmap_get(scores, "Charlie"))

    // Check membership
    println("")
    println("Contains Alice?", hashmap_contains(scores, "Alice"))
    println("Contains Eve?", hashmap_contains(scores, "Eve"))

    // Update a value (overwrite)
    hashmap_insert(scores, "Bob", 91)
    println("")
    println("Bob's updated score:", hashmap_get(scores, "Bob"))

    // Remove a key
    hashmap_remove(scores, "Diana")
    println("After removing Diana, size:", hashmap_len(scores))

    // Get all keys and values
    println("")
    println("All keys:", hashmap_keys(scores))
    println("All values:", hashmap_values(scores))

    // Integer keys work too
    println("")
    let yearly = hashmap_new()
    hashmap_insert(yearly, 2024, "expansion")
    hashmap_insert(yearly, 2025, "consolidation")
    hashmap_insert(yearly, 2026, "growth")
    println("2025 plan:", hashmap_get(yearly, 2025))
}
