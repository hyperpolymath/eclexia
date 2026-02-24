// SPDX-License-Identifier: PMPL-1.0-or-later
// Matrix operations — demonstrates adaptive computation selection.
//
// Different matrix algorithms have different resource profiles.
// The runtime selects the cheapest viable solution.

fn dot_product(a1: Int, a2: Int, a3: Int, b1: Int, b2: Int, b3: Int) -> Int {
    a1 * b1 + a2 * b2 + a3 * b3
}

// Adaptive matrix operation: select algorithm by resource budget
adaptive def matrix_op(n: Int) -> Int
    @requires: energy < 100J
    @requires: carbon < 50gCO2e
    @optimize: minimize energy
{
    @solution "fast_approx":
        @when: true
        @provides: energy: 5J, latency: 1ms, carbon: 1gCO2e
    {
        // O(1) approximation
        n * n
    }

    @solution "exact_compute":
        @when: true
        @provides: energy: 50J, latency: 100ms, carbon: 10gCO2e
    {
        // More accurate: sum of squares
        sum_of_squares(n, 0, 1)
    }
}

fn sum_of_squares(n: Int, acc: Int, i: Int) -> Int {
    if i > n {
        acc
    } else {
        sum_of_squares(n, acc + i * i, i + 1)
    }
}

fn main() {
    println("=== Matrix Operations Demo ===");

    // Direct dot product
    let dp = dot_product(1, 2, 3, 4, 5, 6);
    println("Dot product [1,2,3] . [4,5,6] =", dp);

    // Adaptive matrix operation
    println("");
    println("Adaptive matrix operations (minimize energy):");
    println("  matrix_op(3) =", matrix_op(3));
    println("  matrix_op(5) =", matrix_op(5));
    println("  matrix_op(10) =", matrix_op(10));

    // Direct sum of squares
    println("");
    println("Sum of squares:");
    println("  1^2 + 2^2 + 3^2 =", sum_of_squares(3, 0, 1));
    println("  1^2 + ... + 10^2 =", sum_of_squares(10, 0, 1));

    println("");
    println("Resource budgets enforced:");
    println("  energy < 100J, carbon < 50gCO2e");
    println("  Runtime selected cheapest viable algorithm")
}
