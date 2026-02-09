// SPDX-License-Identifier: PMPL-1.0-or-later
// Mathematical computations in Eclexia

def factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

def power(base: Int, exp: Int) -> Int {
    if exp == 0 {
        1
    } else {
        base * power(base, exp - 1)
    }
}

def gcd(a: Int, b: Int) -> Int {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

def is_prime(n: Int) -> Bool {
    if n < 2 {
        false
    } else {
        let i = 2
        let result = true
        while i * i <= n {
            if n % i == 0 {
                result = false
            }
            i = i + 1
        }
        result
    }
}

def abs(x: Int) -> Int {
    if x < 0 { -x } else { x }
}

def main() -> Unit {
    println("=== Math Showcase ===")

    // Factorials
    println("5! =", factorial(5))
    println("10! =", factorial(10))

    // Powers
    println("2^10 =", power(2, 10))
    println("3^5 =", power(3, 5))

    // GCD
    println("gcd(48, 18) =", gcd(48, 18))
    println("gcd(100, 75) =", gcd(100, 75))

    // Prime checking
    println("")
    println("Primes up to 30:")
    let n = 2
    while n <= 30 {
        if is_prime(n) {
            print(n, "")
        }
        n = n + 1
    }
    println("")

    // Absolute value
    println("")
    println("abs(-42) =", abs(-42))
    println("abs(17) =", abs(17))
}
