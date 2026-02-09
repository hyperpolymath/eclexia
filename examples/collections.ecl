// SPDX-License-Identifier: PMPL-1.0-or-later
// Collection operations in Eclexia

def sum_array(arr: Array[Int]) -> Int {
    let total = 0
    let i = 0
    while i < len(arr) {
        total = total + arr[i]
        i = i + 1
    }
    total
}

def reverse_array(arr: Array[Int]) -> Array[Int] {
    let result = []
    let i = len(arr) - 1
    while i >= 0 {
        result = result + [arr[i]]
        i = i - 1
    }
    result
}

def main() -> Unit {
    println("=== Collections Demo ===")

    // Array operations
    let numbers = [1, 2, 3, 4, 5]
    println("Array:", numbers)
    println("Length:", len(numbers))
    println("Sum:", sum_array(numbers))
    println("First:", numbers[0])
    println("Last:", numbers[4])

    // Array construction
    let doubled = []
    let i = 0
    while i < len(numbers) {
        doubled = doubled + [numbers[i] * 2]
        i = i + 1
    }
    println("Doubled:", doubled)
    println("Reversed:", reverse_array(numbers))

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

    // Tuple operations
    let point = (3, 4)
    println("")
    println("Tuple:", point)
}
