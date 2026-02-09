// SPDX-License-Identifier: PMPL-1.0-or-later
// For loops with ranges in Eclexia

def fizzbuzz(n: Int) -> String {
    if n % 15 == 0 {
        "FizzBuzz"
    } else if n % 3 == 0 {
        "Fizz"
    } else if n % 5 == 0 {
        "Buzz"
    } else {
        to_string(n)
    }
}

def main() -> Unit {
    println("=== Range Loops Demo ===")

    // Simple range loop
    println("Counting 1 to 5:")
    for i in range(1, 6) {
        print(i, "")
    }
    println("")

    // Accumulator pattern
    let sum = 0
    for i in range(1, 101) {
        sum = sum + i
    }
    println("Sum 1..100 =", sum)

    // Nested loops
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
