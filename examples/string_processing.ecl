// SPDX-License-Identifier: PMPL-1.0-or-later
// String processing in Eclexia

def repeat_string(s: String, n: Int) -> String {
    let result = ""
    let i = 0
    while i < n {
        result = result + s
        i = i + 1
    }
    result
}

def is_palindrome(s: String) -> Bool {
    let chars = to_string(s)
    let n = len(s)
    let i = 0
    while i < n / 2 {
        // Simplified: compare character positions
        // In full Eclexia, string indexing would be supported
        i = i + 1
    }
    true  // Simplified for demo
}

def main() -> Unit {
    println("=== String Processing Demo ===")

    let greeting = "Hello"
    let name = "Eclexia"
    let message = greeting + ", " + name + "!"
    println(message)

    // String length
    println("Length of greeting:", len(greeting))

    // String repetition
    let stars = repeat_string("*", 20)
    println(stars)

    // String conversion
    let num = 42
    println("Number as string:", to_string(num))

    // Multi-line output
    let separator = repeat_string("-", 30)
    println(separator)
    println("  String operations work!")
    println(separator)
}
