// SPDX-License-Identifier: PMPL-1.0-or-later
// Pattern matching in Eclexia

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

fn classify(n: Int) -> String {
    match n {
        0 => "zero",
        1 => "one",
        2 => "two",
        _ => "many",
    }
}

fn sign(x: Int) -> String {
    if x > 0 {
        "positive"
    } else {
        if x < 0 {
            "negative"
        } else {
            "zero"
        }
    }
}

fn main() {
    println("=== Pattern Matching Demo ===")

    // Enum variant matching
    println("Red:", color_name(Red))
    println("Green:", color_name(Green))
    println("Blue:", color_name(Blue))

    // Integer literal matching with wildcard
    println("")
    println("classify(0):", classify(0))
    println("classify(1):", classify(1))
    println("classify(42):", classify(42))

    // If-expression as pattern alternative
    println("")
    println("sign(5):", sign(5))
    println("sign(-3):", sign(-3))
    println("sign(0):", sign(0))

    // Match on boolean
    let flag = true
    let desc = match flag {
        true => "yes",
        false => "no",
    }
    println("")
    println("flag:", desc)

    // Nested match
    let x = 5
    let result = match x {
        0 => "nothing",
        _ => match x {
            1 => "single",
            _ => "multiple",
        },
    }
    println("nested match:", result)
}
