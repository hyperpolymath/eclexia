// SPDX-License-Identifier: PMPL-1.0-or-later
// Example: Macro system demonstration
// Shows Eclexia's hygienic macro definitions and invocations.

macro debug_print {
    ($val:expr) => {
        println("DEBUG:", $val)
    }
}

macro assert_eq {
    ($left:expr, $right:expr) => {
        if $left == $right {
            println("PASS:", to_string($left), "==", to_string($right))
        } else {
            println("FAIL:", to_string($left), "!=", to_string($right))
        }
    }
}

macro unless {
    ($cond:expr, $body:expr) => {
        if !$cond {
            $body
        }
    }
}

fn main() {
    println("=== Macros Demo ===")

    // Simple debug printing macro
    debug_print!(42)
    debug_print!("hello from macro")
    debug_print!(3.14)

    // Assertion macro
    println("")
    println("Assertions:")
    assert_eq!(2 + 2, 4)
    assert_eq!(10 * 3, 30)
    assert_eq!(true, true)

    // Control flow macro
    println("")
    println("Control flow macros:")
    let x = 5
    unless!(x > 10, println("x is not greater than 10"))
    unless!(x < 0, println("x is not negative"))
}
