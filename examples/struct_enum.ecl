// SPDX-License-Identifier: PMPL-1.0-or-later
// Struct and enum definitions in Eclexia

type Point = { x: Float, y: Float }

type Color = enum {
    Red,
    Green,
    Blue,
    Custom(Int, Int, Int),
}

def distance(a: Point, b: Point) -> Float {
    let dx = b.x - a.x
    let dy = b.y - a.y
    // Approximate sqrt using Newton's method
    let sq = dx * dx + dy * dy
    if sq == 0.0 {
        0.0
    } else {
        let x = sq / 2.0
        x = (x + sq / x) / 2.0
        x = (x + sq / x) / 2.0
        x = (x + sq / x) / 2.0
        x = (x + sq / x) / 2.0
        x
    }
}

def color_name(c: Color) -> String {
    match c {
        Red => "red",
        Green => "green",
        Blue => "blue",
        Custom(r, g, b) => "custom",
    }
}

def midpoint(a: Point, b: Point) -> Point {
    Point {
        x: (a.x + b.x) / 2.0,
        y: (a.y + b.y) / 2.0,
    }
}

def main() -> Unit {
    println("=== Struct & Enum Demo ===")

    // Struct creation and field access
    let origin = Point { x: 0.0, y: 0.0 }
    let p = Point { x: 3.0, y: 4.0 }
    println("Origin:", origin)
    println("Point p:", p)
    println("p.x =", p.x)
    println("p.y =", p.y)

    // Distance calculation
    let d = distance(origin, p)
    println("Distance from origin to p:", d)

    // Midpoint
    let mid = midpoint(origin, p)
    println("Midpoint:", mid)

    // Enum variants
    println("")
    let c1 = Red
    let c2 = Custom(128, 64, 255)
    println("Color 1:", color_name(c1))
    println("Color 2:", color_name(c2))
}
