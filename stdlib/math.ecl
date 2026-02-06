// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Math module providing mathematical functions and constants.

// Mathematical constants
const PI: Float = 3.141592653589793
const E: Float = 2.718281828459045
const TAU: Float = 6.283185307179586  // 2 * PI

// Basic functions
fn abs_int(x: Int) -> Int {
    if x < 0 { -x } else { x }
}

fn abs_float(x: Float) -> Float {
    if x < 0.0 { -x } else { x }
}

fn min_int(a: Int, b: Int) -> Int {
    if a < b { a } else { b }
}

fn max_int(a: Int, b: Int) -> Int {
    if a > b { a } else { b }
}

fn min_float(a: Float, b: Float) -> Float {
    if a < b { a } else { b }
}

fn max_float(a: Float, b: Float) -> Float {
    if a > b { a } else { b }
}

// Power and roots
fn pow_int(base: Int, exp: Int) -> Int {
    if exp == 0 {
        1
    } else if exp == 1 {
        base
    } else if exp % 2 == 0 {
        let half = pow_int(base, exp / 2)
        half * half
    } else {
        base * pow_int(base, exp - 1)
    }
}

fn sqrt(x: Float) -> Float {
    @builtin("sqrt")
}

fn cbrt(x: Float) -> Float {
    @builtin("cbrt")
}

// Trigonometric functions
fn sin(x: Float) -> Float {
    @builtin("sin")
}

fn cos(x: Float) -> Float {
    @builtin("cos")
}

fn tan(x: Float) -> Float {
    @builtin("tan")
}

fn asin(x: Float) -> Float {
    @builtin("asin")
}

fn acos(x: Float) -> Float {
    @builtin("acos")
}

fn atan(x: Float) -> Float {
    @builtin("atan")
}

fn atan2(y: Float, x: Float) -> Float {
    @builtin("atan2")
}

// Hyperbolic functions
fn sinh(x: Float) -> Float {
    @builtin("sinh")
}

fn cosh(x: Float) -> Float {
    @builtin("cosh")
}

fn tanh(x: Float) -> Float {
    @builtin("tanh")
}

// Exponential and logarithmic functions
fn exp(x: Float) -> Float {
    @builtin("exp")
}

fn ln(x: Float) -> Float {
    @builtin("ln")
}

fn log10(x: Float) -> Float {
    @builtin("log10")
}

fn log2(x: Float) -> Float {
    @builtin("log2")
}

fn log(x: Float, base: Float) -> Float {
    ln(x) / ln(base)
}

// Rounding functions
fn floor(x: Float) -> Float {
    @builtin("floor")
}

fn ceil(x: Float) -> Float {
    @builtin("ceil")
}

fn round(x: Float) -> Float {
    @builtin("round")
}

fn trunc(x: Float) -> Float {
    @builtin("trunc")
}

// Factorial
fn factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// GCD and LCM
fn gcd(a: Int, b: Int) -> Int {
    if b == 0 {
        abs_int(a)
    } else {
        gcd(b, a % b)
    }
}

fn lcm(a: Int, b: Int) -> Int {
    if a == 0 || b == 0 {
        0
    } else {
        abs_int(a * b) / gcd(a, b)
    }
}

// Clamping
fn clamp_int(value: Int, min: Int, max: Int) -> Int {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}

fn clamp_float(value: Float, min: Float, max: Float) -> Float {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}
