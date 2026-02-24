// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Infinite type expansion
type Infinite<T> = Infinite<Infinite<T>>

fn main() {
    let x: Infinite<int> = ???;
}
