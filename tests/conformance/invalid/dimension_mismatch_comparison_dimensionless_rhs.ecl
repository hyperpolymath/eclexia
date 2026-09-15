// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional mismatch in comparison, dimensionless operand on the right
// Expected: Type error - comparing a Resource<Energy> to a bare Float
// (ADR-001 section 2.2.2: "energy < 100 and energy < 100J are today the
// same program" — this must be rejected, not silently accepted.)

fn test() -> bool {
    let energy: Resource<Energy> = 100J;

    // This should fail: comparing a dimensioned resource to a dimensionless
    // literal, with no unit named.
    energy > 1.0
}
