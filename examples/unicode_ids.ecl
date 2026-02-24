// SPDX-License-Identifier: PMPL-1.0-or-later
// Unicode identifiers in Eclexia

fn π() -> Float {
    3.141592653589793
}

fn τ() -> Float {
    2.0 * π()
}

fn 面積(半径: Float) -> Float {
    π() * 半径 * 半径
}

fn αβγ(x: Float, y: Float, z: Float) -> Float {
    x + y + z
}

fn main() {
    println("=== Unicode Identifiers Demo ===")

    let r = 5.0
    println("π =", π())
    println("τ =", τ())
    println("Area of circle with r=5:", 面積(r))

    // Greek letters as variable names
    let α = 1.0
    let β = 2.0
    let γ = 3.0
    println("α + β + γ =", αβγ(α, β, γ))

    // Math notation
    let Δx = 10.0
    let Δy = 20.0
    println("Δx =", Δx, "Δy =", Δy)
}
