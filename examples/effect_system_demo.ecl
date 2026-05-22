// SPDX-License-Identifier: MPL-2.0
// Effect system syntax demo (handlers are currently no-ops in the runtime).

effect Logger {
    log(message: String);
}

fn compute(n: Int) -> Int {
    n * 2 + 1
}

fn main() {
    println("=== Effect System Demo ===")

    // NOTE: Effect handlers are parsed and type-checked, but not executed yet.
    let result = handle compute(20) {
        Logger::log(message: String) => {
            println("handled log:", message)
        }
    }

    println("compute(20) =", result)
}
