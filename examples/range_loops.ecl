// SPDX-License-Identifier: PMPL-1.0-or-later
// Loops and iteration in Eclexia

fn fizzbuzz(n: Int) -> String {
    if n % 15 == 0 {
        "FizzBuzz"
    } else {
        if n % 3 == 0 {
            "Fizz"
        } else {
            if n % 5 == 0 {
                "Buzz"
            } else {
                to_string(n)
            }
        }
    }
}

fn main() {
    println("=== Loops Demo ===")

    // Range-based for loop
    println("Counting 1 to 5:")
    for i in range(1, 6) {
        print(i, "")
    }
    println("")

    // Accumulator with while
    let sum = 0
    let i = 1
    while i <= 100 {
        sum = sum + i
        i = i + 1
    }
    println("Sum 1..100 =", sum)

    // Nested loops for multiplication table
    println("")
    println("Multiplication table (1-5):")
    for i in range(1, 6) {
        for j in range(1, 6) {
            print(i * j, "\t")
        }
        println("")
    }

    // FizzBuzz
    println("")
    println("FizzBuzz (1-20):")
    for i in range(1, 21) {
        print(fizzbuzz(i), " ")
    }
    println("")
}
