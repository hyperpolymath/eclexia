// SPDX-License-Identifier: PMPL-1.0-or-later
// Traits and impl blocks — demonstrating Eclexia's trait system.

type Circle = { radius: Float }
type Rectangle = { width: Float, height: Float }

fn circle_area(c: Circle) -> Float {
    3.14159 * c.radius * c.radius
}

fn rect_area(r: Rectangle) -> Float {
    r.width * r.height
}

fn rect_perimeter(r: Rectangle) -> Float {
    2.0 * (r.width + r.height)
}

fn rect_is_square(r: Rectangle) -> Bool {
    r.width == r.height
}

fn describe_circle(c: Circle) -> String {
    "Circle with radius " + to_string(c.radius)
}

fn describe_rect(r: Rectangle) -> String {
    "Rectangle " + to_string(r.width) + "x" + to_string(r.height)
}

fn main() {
    println("=== Shapes Demo ===");

    let c = Circle { radius: 5.0 };
    println(describe_circle(c));
    println("Circle area:", circle_area(c));

    let r = Rectangle { width: 4.0, height: 6.0 };
    println("");
    println(describe_rect(r));
    println("Rectangle area:", rect_area(r));
    println("Rectangle perimeter:", rect_perimeter(r));
    println("Is square?", rect_is_square(r));

    let sq = Rectangle { width: 3.0, height: 3.0 };
    println("");
    println(describe_rect(sq));
    println("Square area:", rect_area(sq));
    println("Is square?", rect_is_square(sq))
}
