// SPDX-License-Identifier: PMPL-1.0-or-later
// Collection operations in Eclexia

fn main() {
    println("=== Collections Demo ===")

    // Array creation and indexing
    let numbers = [1, 2, 3, 4, 5]
    println("Array:", numbers)
    println("Length:", len(numbers))
    println("First:", numbers[0])
    println("Last:", numbers[4])

    // Sum via loop
    let sum = 0
    let i = 0
    while i < len(numbers) {
        sum = sum + numbers[i]
        i = i + 1
    }
    println("Sum:", sum)

    // Array repeat
    let zeros = [0; 5]
    println("Zeros:", zeros)

    // HashMap operations
    let scores = hashmap_new()
    hashmap_insert(scores, "Alice", 95)
    hashmap_insert(scores, "Bob", 87)
    hashmap_insert(scores, "Carol", 92)

    println("")
    println("HashMap:")
    println("  Alice:", hashmap_get(scores, "Alice"))
    println("  Bob:", hashmap_get(scores, "Bob"))
    println("  Size:", hashmap_len(scores))
    println("  Has 'Alice':", hashmap_contains(scores, "Alice"))
    println("  Has 'Dave':", hashmap_contains(scores, "Dave"))

    // Tuple operations
    let point = (3, 4)
    println("")
    println("Tuple:", point)
}
