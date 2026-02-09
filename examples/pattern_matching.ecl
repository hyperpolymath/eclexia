// SPDX-License-Identifier: PMPL-1.0-or-later
// Pattern matching and destructuring in Eclexia

type Shape = enum {
    Circle(Float),
    Rectangle(Float, Float),
    Triangle(Float, Float, Float),
}

def area(shape: Shape) -> Float {
    match shape {
        Circle(r) => 3.14159 * r * r,
        Rectangle(w, h) => w * h,
        Triangle(a, b, c) => {
            // Heron's formula
            let s = (a + b + c) / 2.0
            let sq = s * (s - a) * (s - b) * (s - c)
            // Approximate square root using Newton's method
            let x = sq / 2.0
            let x = (x + sq / x) / 2.0
            let x = (x + sq / x) / 2.0
            let x = (x + sq / x) / 2.0
            x
        },
    }
}

def describe(shape: Shape) -> String {
    match shape {
        Circle(_) => "circle",
        Rectangle(_, _) => "rectangle",
        Triangle(_, _, _) => "triangle",
    }
}

def main() -> Unit {
    println("=== Pattern Matching Demo ===")

    let c = Circle(5.0)
    let r = Rectangle(3.0, 4.0)

    println("Shape:", describe(c), "area:", area(c))
    println("Shape:", describe(r), "area:", area(r))

    // Nested match with literals
    let x = 42
    let result = match x {
        0 => "zero",
        1 => "one",
        42 => "the answer",
        _ => "other",
    }
    println("Match result:", result)
}
