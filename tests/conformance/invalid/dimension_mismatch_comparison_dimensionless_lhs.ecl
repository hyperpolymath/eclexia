// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

// Test: Dimensional mismatch in comparison, dimensionless operand on the left
// Expected: Type error - comparing a bare Float to a Resource<Energy>
// (symmetric case of dimension_mismatch_comparison_dimensionless_rhs.ecl —
// the dimensionless operand can appear on either side of the operator).

fn test() -> bool {
    let energy: Resource<Energy> = 100J;

    // This should fail: comparing a dimensionless literal to a dimensioned
    // resource, with no unit named.
    1.0 < energy
}
