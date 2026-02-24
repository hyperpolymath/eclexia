// SPDX-License-Identifier: PMPL-1.0-or-later
// Dimensional type system — demonstrates resource-typed computation.
//
// Eclexia tracks physical dimensions (energy, time, carbon, memory)
// as first-class types. Functions declare resource constraints via
// @requires annotations; the type checker verifies dimensional consistency.

// Pure math: no resource annotations needed
fn calculate_power(energy: Float, time: Float) -> Float {
    // Power = Energy / Time (Watts)
    energy / time
}

fn calculate_kinetic_energy(mass: Float, velocity: Float) -> Float {
    // KE = 0.5 * m * v^2
    0.5 * mass * velocity * velocity
}

// A function with tight energy and carbon constraints
def efficient_compute(n: Int) -> Int
    @requires: energy < 5J
    @requires: carbon < 1gCO2e
{
    // O(1) closed-form — minimal resource usage
    n * (n + 1) / 2
}

// Adaptive: choose algorithm based on resource budget
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "tail_recursive":
        @when: true
        @provides: energy: 5J, latency: 10ms, carbon: 1gCO2e
    {
        fib_tail(n, 0, 1)
    }

    @solution "naive_recursive":
        @when: true
        @provides: energy: 80J, latency: 500ms, carbon: 10gCO2e
    {
        fib_naive(n)
    }
}

fn fib_tail(n: Int, a: Int, b: Int) -> Int {
    if n <= 0 {
        a
    } else {
        fib_tail(n - 1, b, a + b)
    }
}

fn fib_naive(n: Int) -> Int {
    if n <= 1 {
        n
    } else {
        fib_naive(n - 1) + fib_naive(n - 2)
    }
}

fn main() {
    println("=== Dimensional Types Demo ===");

    // Pure calculations
    let power = calculate_power(100.0, 10.0);
    println("Power (100J / 10s):", power, "W");

    let ke = calculate_kinetic_energy(2.0, 3.0);
    println("Kinetic energy (2kg, 3m/s):", ke, "J");

    // Tight-budget computation
    let sum = efficient_compute(100);
    println("Sum 1..100 =", sum);

    // Adaptive fibonacci
    println("");
    println("Adaptive fibonacci (minimize energy):");
    println("  fib(0) =", fibonacci(0));
    println("  fib(5) =", fibonacci(5));
    println("  fib(10) =", fibonacci(10));

    println("");
    println("Resource constraints enforced:");
    println("  efficient_compute: energy < 5J, carbon < 1gCO2e");
    println("  fibonacci: energy < 100J, optimize minimize energy")
}
