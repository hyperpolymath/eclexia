// SPDX-License-Identifier: PMPL-1.0-or-later
// Example: Type system features
// Demonstrates generic functions and type inference.

fn identity<T>(x: T) -> T {
    x
}

fn first<A, B>(a: A, b: B) -> A {
    a
}

fn second<A, B>(a: A, b: B) -> B {
    b
}

fn apply_twice<T>(f: fn(T) -> T, x: T) -> T {
    f(f(x))
}

fn double(x: Int) -> Int {
    x * 2
}

fn exclaim(s: String) -> String {
    s + "!"
}

fn main() {
    println("=== Type System Demo ===")

    // Generic identity works with any type
    println("Generic identity:")
    println("  identity(42) =", identity(42))
    println("  identity(true) =", identity(true))
    println("  identity(3.14) =", identity(3.14))
    println("  identity(\"hello\") =", identity("hello"))

    // Generic pair selection
    println("")
    println("Generic pairs:")
    println("  first(1, \"a\") =", first(1, "a"))
    println("  second(1, \"a\") =", second(1, "a"))
    println("  first(true, 42) =", first(true, 42))
    println("  second(true, 42) =", second(true, 42))

    // Higher-order generics
    println("")
    println("Higher-order generics:")
    println("  apply_twice(double, 3) =", apply_twice(double, 3))

    // Type inference
    println("")
    println("Type inference:")
    let x = 42
    let y = 3.14
    let z = "inferred as string"
    let w = true
    let arr = [1, 2, 3, 4, 5]
    println("  x =", x)
    println("  y =", y)
    println("  z =", z)
    println("  w =", w)
    println("  arr =", arr)
    println("  len(arr) =", len(arr))
}
