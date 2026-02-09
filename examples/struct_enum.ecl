// SPDX-License-Identifier: PMPL-1.0-or-later
// Struct and enum definitions in Eclexia

type Point = { x: Float, y: Float }

type Color = enum {
    Red,
    Green,
    Blue,
}

fn color_name(c: Color) -> String {
    match c {
        Red => "red",
        Green => "green",
        Blue => "blue",
    }
}

fn midpoint(ax: Float, ay: Float, bx: Float, by: Float) -> Point {
    Point {
        x: (ax + bx) / 2.0,
        y: (ay + by) / 2.0,
    }
}

fn main() {
    println("=== Struct & Enum Demo ===")

    // Struct creation and field access
    let origin = Point { x: 0.0, y: 0.0 }
    let p = Point { x: 3.0, y: 4.0 }
    println("Origin:", origin)
    println("Point p:", p)
    println("p.x =", p.x)
    println("p.y =", p.y)

    // Computed struct
    let mid = midpoint(0.0, 0.0, 6.0, 8.0)
    println("Midpoint:", mid)

    // Enum variants
    println("")
    println("Color Red:", color_name(Red))
    println("Color Green:", color_name(Green))
    println("Color Blue:", color_name(Blue))

    // Struct with different values
    let q = Point { x: -1.5, y: 2.7 }
    println("")
    println("Point q:", q)
    println("q.x =", q.x)
    println("q.y =", q.y)
}
