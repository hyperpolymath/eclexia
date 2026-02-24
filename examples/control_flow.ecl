// SPDX-License-Identifier: PMPL-1.0-or-later
// Control flow constructs in Eclexia

fn collatz_steps(n: Int) -> Int {
    let steps = 0
    let current = n
    while current != 1 {
        if current % 2 == 0 {
            current = current / 2
        } else {
            current = 3 * current + 1
        }
        steps = steps + 1
    }
    steps
}

fn classify(x: Int) -> String {
    if x > 0 {
        if x % 2 == 0 {
            "positive even"
        } else {
            "positive odd"
        }
    } else {
        if x < 0 {
            "negative"
        } else {
            "zero"
        }
    }
}

fn main() {
    println("=== Control Flow Demo ===")

    // If/else expression with nested branches
    let score = 85
    let grade = if score >= 90 {
        "A"
    } else {
        if score >= 80 {
            "B"
        } else {
            if score >= 70 {
                "C"
            } else {
                "F"
            }
        }
    }
    println("Score:", score, "Grade:", grade)

    // Collatz conjecture
    println("")
    println("Collatz conjecture (steps to reach 1):")
    let n = 1
    while n <= 15 {
        println("  n =", n, "steps =", collatz_steps(n))
        n = n + 1
    }

    // Classification
    println("")
    println("15 is", classify(15))
    println("-3 is", classify(-3))
    println("0 is", classify(0))
    println("8 is", classify(8))
}
