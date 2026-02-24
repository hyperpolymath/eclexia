// SPDX-License-Identifier: PMPL-1.0-or-later
// Error handling with Result and Option types in Eclexia

fn safe_divide(a: Float, b: Float) -> Result[Float, String] {
    if b == 0.0 {
        Err("division by zero")
    } else {
        Ok(a / b)
    }
}

fn main() {
    println("=== Error Handling Demo ===")

    // Result type usage
    let r1 = safe_divide(10.0, 3.0)
    let r2 = safe_divide(10.0, 0.0)
    println("10 / 3 =", r1)
    println("10 / 0 =", r2)

    // Option construction
    let some_val = Some(42)
    let no_val = None
    println("")
    println("Some(42):", some_val)
    println("None:", no_val)

    // Chained safe operations
    let r3 = safe_divide(100.0, 5.0)
    let r4 = safe_divide(100.0, 0.0)
    println("")
    println("100 / 5 =", r3)
    println("100 / 0 =", r4)

    // Multiple divisions
    println("")
    println("Dividing 1000 by successive values:")
    let d = 1.0
    while d <= 5.0 {
        let result = safe_divide(1000.0, d)
        println("  1000 /", d, "=", result)
        d = d + 1.0
    }
}
