fn factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn power(base: Int, exp: Int) -> Int {
    if exp == 0 {
        1
    } else {
        base * power(base, exp - 1)
    }
}

fn gcd(a: Int, b: Int) -> Int {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn is_prime_helper(n: Int, i: Int) -> Bool {
    if i * i > n {
        true
    } else {
        if n % i == 0 {
            false
        } else {
            is_prime_helper(n, i + 1)
        }
    }
}

fn is_prime(n: Int) -> Bool {
    if n < 2 {
        false
    } else {
        is_prime_helper(n, 2)
    }
}

fn abs(x: Int) -> Int {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn main() {
    println("=== Math Showcase ===");
    println("5! =", factorial(5));
    println("10! =", factorial(10));
    println("2^10 =", power(2, 10));
    println("3^5 =", power(3, 5));
    println("gcd(48, 18) =", gcd(48, 18));
    println("gcd(100, 75) =", gcd(100, 75));
    println("");
    println("Primes up to 30:");
    let n = 2;
    while n <= 30 {
        if is_prime(n) {
            print(n, "")
        };
        n = n + 1;
    }
    println("");
    println("");
    println("abs(-42) =", abs(-42));
    println("abs(17) =", abs(17))
}
