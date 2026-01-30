// SPDX-License-Identifier: PMPL-1.0-or-later
// Dimensional Type Checking Example

// Example 1: Energy calculations with proper dimensions
fn calculate_power_consumption() -> Float[kg·m^2/s^3] {
    let energy: Float[kg·m^2/s^2] = 100.0  // 100 Joules
    let time: Float[s] = 10.0              // 10 seconds

    // Energy / Time = Power (kg·m²/s³)
    energy / time  // Returns power in Watts
}

// Example 2: This would cause a dimension mismatch error
fn incorrect_addition() {
    let energy: Float[kg·m^2/s^2] = 50.0   // Energy in Joules
    let time: Float[s] = 5.0                // Time in seconds

    // ERROR: Cannot add energy and time (different dimensions)
    // let result = energy + time
}

// Example 3: Adaptive function with resource constraints
adaptive fn fibonacci(n: Int) -> Int
    @requires time < 1s
    @requires energy < 100J
    @optimize minimize(energy)
{
    solution iterative
        @when n < 30
        @provides energy = 10J, time = 50ms
    {
        let mut a = 0
        let mut b = 1
        let mut i = 0

        while i < n {
            let temp = a + b
            a = b
            b = temp
            i = i + 1
        }
        a
    }

    solution recursive
        @when n >= 30
        @provides energy = 80J, time = 500ms
    {
        if n <= 1 {
            n
        } else {
            fibonacci(n - 1) + fibonacci(n - 2)
        }
    }
}

// Example 4: Correct dimensional arithmetic
fn dimensional_algebra() {
    let distance: Float[m] = 100.0         // 100 meters
    let time: Float[s] = 10.0              // 10 seconds

    // distance / time = velocity (m/s)
    let velocity = distance / time

    // velocity * time = distance (m)
    let distance_check = velocity * time

    // acceleration = velocity / time (m/s²)
    let acceleration = velocity / time

    println("Distance: {}m", distance)
    println("Velocity: {}m/s", velocity)
    println("Acceleration: {}m/s²", acceleration)
}

// Example 5: Scalar multiplication preserves dimensions
fn scalar_operations() {
    let energy: Float[kg·m^2/s^2] = 50.0   // 50 Joules
    let scale = 2.0                         // Dimensionless scalar

    // Scalar multiplication preserves dimension
    let doubled_energy = energy * scale    // Still in Joules

    // Division by scalar also preserves dimension
    let halved_energy = energy / scale     // Still in Joules
}
