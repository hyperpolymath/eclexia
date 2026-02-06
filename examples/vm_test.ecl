// Simple test for bytecode VM execution
// This will be compiled to bytecode and executed

fn add(a: Int, b: Int) -> Int {
    a + b
}

fn main() -> Int {
    let x = 5
    let y = 10
    add(x, y)
}
