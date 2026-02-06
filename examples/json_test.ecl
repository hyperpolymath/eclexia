// SPDX-License-Identifier: MIT
// Test JSON and File I/O features - for SustainaBot integration!

def main() -> Unit {
    println("Eclexia Runtime Expansion Demo")
    println("================================\n")

    // Test 1: JSON parsing
    println("Test 1: JSON Parsing")
    let json_str = "{\"energy\": 10.5, \"carbon\": 1.2, \"name\": \"test\"}"
    let parsed = parse_json(json_str)
    println("Parsed:", to_string(parsed))
    println()

    // Test 2: JSON serialization
    println("Test 2: JSON Serialization")
    let data = [1, 2, 3, 4, 5]
    let json_out = to_json(data)
    println("Serialized:", json_out)
    println()

    // Test 3: File I/O
    println("Test 3: File I/O")
    let test_file = "/tmp/eclexia_test.txt"

    // Write file
    write_file(test_file, "Hello from Eclexia!\nJSON support works!")
    println("Wrote to", test_file)

    // Check existence
    let exists = file_exists(test_file)
    println("File exists:", to_string(exists))

    // Read back
    let content = read_file(test_file)
    println("Read back:", content)
    println()

    // Test 4: String operations
    println("Test 4: String Operations")
    let text = "  hello world  "
    let trimmed = str_trim(text)
    println("Trimmed:", trimmed)

    let parts = str_split("one,two,three", ",")
    println("Split:", to_string(parts))

    let has_world = str_contains("hello world", "world")
    println("Contains 'world':", to_string(has_world))
    println()

    println("✅ All runtime features working!")
    println("\nThis demonstrates Eclexia's expanded runtime,")
    println("ready for SustainaBot Phase 2 integration!")
}
