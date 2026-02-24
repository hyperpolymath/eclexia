// SPDX-License-Identifier: PMPL-1.0-or-later
// Generics — demonstrating generic functions and type parameters.

fn identity<T>(x: T) -> T {
    x
}

fn first<A, B>(a: A, b: B) -> A {
    a
}

fn second<A, B>(a: A, b: B) -> B {
    b
}

fn apply<T, R>(f: (T) -> R, x: T) -> R {
    f(x)
}

fn double(x: Int) -> Int {
    x * 2
}

fn add_one(x: Int) -> Int {
    x + 1
}

fn main() {
    println("=== Generics ===");

    // identity works on any type
    println("identity(42) =", identity(42));
    println("identity(true) =", identity(true));
    println("identity(\"hello\") =", identity("hello"));

    // first/second select from pairs
    println("first(1, \"two\") =", first(1, "two"));
    println("second(1, \"two\") =", second(1, "two"));

    // higher-order generics
    println("apply(double, 21) =", apply(double, 21))
}
