// SPDX-License-Identifier: MIT
// Example test file demonstrating the testing framework

def add(x: Int, y: Int) -> Int {
    x + y
}

def multiply(x: Int, y: Int) -> Int {
    x * y
}

#[test]
def test_addition() -> Bool {
    add(2, 3) == 5
}

#[test]
def test_multiplication() -> Bool {
    multiply(3, 4) == 12
}

#[test]
def test_zero_addition() -> Bool {
    add(0, 5) == 5
}

#[test]
#[ignore]
def test_ignored_example() -> Bool {
    // This test will be skipped
    false
}

#[test]
def test_should_fail() -> Bool {
    // This test intentionally fails to demonstrate failure reporting
    add(2, 2) == 5
}
