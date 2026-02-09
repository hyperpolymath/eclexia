// SPDX-License-Identifier: PMPL-1.0-or-later
// Control flow constructs in Eclexia

def collatz_steps(n: Int) -> Int {
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

def main() -> Unit {
    println("=== Control Flow Demo ===")

    // If/else chains
    let score = 85
    let grade = if score >= 90 {
        "A"
    } else if score >= 80 {
        "B"
    } else if score >= 70 {
        "C"
    } else {
        "F"
    }
    println("Score:", score, "Grade:", grade)

    // While loops with early exit simulation
    println("")
    println("Collatz conjecture (steps to reach 1):")
    let n = 1
    while n <= 20 {
        let steps = collatz_steps(n)
        println("  n =", n, "steps =", steps)
        n = n + 1
    }

    // Nested conditionals
    println("")
    let x = 15
    let classification = if x > 0 {
        if x % 2 == 0 {
            "positive even"
        } else {
            "positive odd"
        }
    } else if x < 0 {
        "negative"
    } else {
        "zero"
    }
    println(x, "is", classification)
}
