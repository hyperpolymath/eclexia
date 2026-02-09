// SPDX-License-Identifier: PMPL-1.0-or-later
// Unicode identifiers in Eclexia

def π() -> Float {
    3.141592653589793
}

def τ() -> Float {
    2.0 * π()
}

def 面積(半径: Float) -> Float {
    π() * 半径 * 半径
}

def αβγ(x: Float, y: Float, z: Float) -> Float {
    x + y + z
}

def main() -> Unit {
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

    // Emoji-free but expressive math
    let Δx = 10.0
    let Δy = 20.0
    println("Δx =", Δx, "Δy =", Δy)
}
