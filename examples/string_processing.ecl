// SPDX-License-Identifier: PMPL-1.0-or-later
// String processing in Eclexia

fn main() {
    println("=== String Processing Demo ===")

    let greeting = "Hello"
    let name = "Eclexia"
    let message = greeting + ", " + name + "!"
    println(message)

    // String length
    println("Length of greeting:", len(greeting))

    // String repetition via loop
    let stars = ""
    let i = 0
    while i < 20 {
        stars = stars + "*"
        i = i + 1
    }
    println(stars)

    // String conversion
    let num = 42
    println("Number as string:", to_string(num))

    // Build a separator
    let sep = ""
    i = 0
    while i < 30 {
        sep = sep + "-"
        i = i + 1
    }
    println(sep)
    println("  String operations work!")
    println(sep)
}
