// SPDX-License-Identifier: PMPL-1.0-or-later
// File I/O and string operations — demonstrates builtin capabilities.

fn main() {
    println("=== File I/O & String Operations ===");

    // Test 1: File I/O
    println("");
    println("Test 1: File I/O");
    let test_file = "/tmp/eclexia_io_test.txt";
    let content = "Hello from Eclexia!\nLine 2: Economics as Code.";

    write_file(test_file, content);
    println("  Wrote to", test_file);

    let exists = file_exists(test_file);
    println("  File exists:", exists);

    let read_back = read_file(test_file);
    println("  Read back:", read_back);

    // Test 2: String operations
    println("");
    println("Test 2: String Operations");
    let greeting = "Hello, World!";
    println("  String:", greeting);
    println("  Length:", len(greeting));

    // String concatenation
    let first = "Eclexia";
    let second = " is economics-as-code";
    let combined = first + second;
    println("  Combined:", combined);

    // String conversion
    let num = 42;
    let num_str = to_string(num);
    println("  Number as string:", num_str);

    let pi = 3.14159;
    let pi_str = to_string(pi);
    println("  Float as string:", pi_str);

    // Test 3: Boolean logic
    println("");
    println("Test 3: Boolean & Comparison");
    let x = 10;
    let y = 20;
    println("  x =", x, ", y =", y);
    println("  x < y:", x < y);
    println("  x == y:", x == y);
    println("  x + y =", x + y);
    println("  max(x, y) =", max(x, y));
    println("  min(x, y) =", min(x, y));

    println("");
    println("All I/O and string operations working!")
}
