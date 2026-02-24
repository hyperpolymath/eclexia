// SPDX-License-Identifier: PMPL-1.0-or-later

// Test: Arrays with resource tracking
fn main() {
    let arr = [1, 2, 3, 4, 5];
    let sum = arr[0] + arr[4];
    assert(sum == 6);
}
