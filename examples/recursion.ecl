// SPDX-License-Identifier: PMPL-1.0-or-later
// Example: Recursive algorithms
// Classic recursive algorithms beyond fibonacci.

// Tower of Hanoi
fn hanoi(n: Int, from: String, to: String, via: String) {
    if n == 1 {
        println("  Move disk 1 from", from, "to", to)
    } else {
        hanoi(n - 1, from, via, to)
        println("  Move disk", n, "from", from, "to", to)
        hanoi(n - 1, via, to, from)
    }
}

// Sum of digits
fn digit_sum(n: Int) -> Int {
    if n < 10 {
        n
    } else {
        n % 10 + digit_sum(n / 10)
    }
}

// Binary representation (prints MSB first via recursion)
fn print_binary(n: Int) {
    if n > 1 {
        print_binary(n / 2)
    }
    print(to_string(n % 2))
}

// Ackermann function (for small inputs)
fn ackermann(m: Int, n: Int) -> Int {
    if m == 0 {
        n + 1
    } else {
        if n == 0 {
            ackermann(m - 1, 1)
        } else {
            ackermann(m - 1, ackermann(m, n - 1))
        }
    }
}

fn main() {
    println("=== Recursion Demo ===")

    // Tower of Hanoi
    println("Tower of Hanoi (3 disks):")
    hanoi(3, "A", "C", "B")

    // Digit sums
    println("")
    println("Digit sums:")
    println("  digit_sum(123) =", digit_sum(123))
    println("  digit_sum(9999) =", digit_sum(9999))
    println("  digit_sum(10001) =", digit_sum(10001))

    // Binary representation
    println("")
    println("Binary representations:")
    print("  42 in binary: ")
    print_binary(42)
    println("")
    print("  255 in binary: ")
    print_binary(255)
    println("")
    print("  1024 in binary: ")
    print_binary(1024)
    println("")

    // Ackermann function
    println("")
    println("Ackermann function:")
    println("  A(0,0) =", ackermann(0, 0))
    println("  A(1,1) =", ackermann(1, 1))
    println("  A(2,2) =", ackermann(2, 2))
    println("  A(3,3) =", ackermann(3, 3))
}
