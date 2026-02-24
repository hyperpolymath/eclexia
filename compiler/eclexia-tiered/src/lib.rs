// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Tiered execution, profiling, and watch mode for Eclexia.
//!
//! ## Tiered execution
//!
//! Functions start at a low tier and are promoted as they get "hot":
//!
//! | Tier | Backend | Compilation cost | Runtime speed |
//! |------|---------|------------------|---------------|
//! | 0 | Interpreter | None | Slowest |
//! | 1 | Bytecode VM | Fast | Moderate |
//! | 2 | Cranelift | Moderate | Fast |
//! | 3 | LLVM + PGO | Slow | Fastest |
//!
//! ## PGO (Profile-Guided Optimization)
//!
//! Instrumented bytecode collects:
//! - Call counts per function
//! - Branch frequencies
//! - Resource usage patterns
//! - Shadow price histories
//!
//! This data feeds into LLVM for Tier 3 optimization.
//!
//! ## Watch mode
//!
//! File system watching with debounced incremental rebuilds.

pub mod profile;
pub mod tier;
pub mod watch;

#[cfg(test)]
mod tests {
    #[test]
    fn test_crate_compiles() {
        // Smoke test: crate loaded successfully
        assert!(true);
    }
}
