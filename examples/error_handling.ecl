// SPDX-License-Identifier: PMPL-1.0-or-later
// Error handling with Result and Option types in Eclexia

def safe_divide(a: Float, b: Float) -> Result[Float, String] {
    if b == 0.0 {
        Err("division by zero")
    } else {
        Ok(a / b)
    }
}

def find_element(arr: Array[Int], target: Int) -> Option[Int] {
    let i = 0
    while i < len(arr) {
        if arr[i] == target {
            return Some(i)
        }
        i = i + 1
    }
    None
}

def main() -> Unit {
    println("=== Error Handling Demo ===")

    // Result type usage
    let r1 = safe_divide(10.0, 3.0)
    let r2 = safe_divide(10.0, 0.0)
    println("10 / 3 =", r1)
    println("10 / 0 =", r2)

    // Pattern matching on Result
    match r1 {
        Ok(v) => println("  Success:", v),
        Err(e) => println("  Error:", e),
    }

    match r2 {
        Ok(v) => println("  Success:", v),
        Err(e) => println("  Error:", e),
    }

    // Option type usage
    let numbers = [10, 20, 30, 40, 50]
    let found = find_element(numbers, 30)
    let missing = find_element(numbers, 99)

    println("Find 30:", found)
    println("Find 99:", missing)

    match found {
        Some(idx) => println("  Found at index:", idx),
        None => println("  Not found"),
    }
}
