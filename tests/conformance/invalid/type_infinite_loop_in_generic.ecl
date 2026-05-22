// SPDX-License-Identifier: MPL-2.0

// Test: Infinite type expansion
type Infinite<T> = Infinite<Infinite<T>>

fn main() {
    let x: Infinite<int> = ???;
}
