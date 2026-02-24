// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Breakpoint management.

use std::collections::HashSet;

/// Breakpoint manager.
#[derive(Debug, Clone)]
pub struct BreakpointManager {
    /// Active breakpoints (function_idx, instruction_idx)
    breakpoints: HashSet<(usize, usize)>,
}

impl BreakpointManager {
    /// Create a new breakpoint manager.
    pub fn new() -> Self {
        Self {
            breakpoints: HashSet::new(),
        }
    }

    /// Set a breakpoint.
    pub fn set(&mut self, func_idx: usize, inst_idx: usize) {
        self.breakpoints.insert((func_idx, inst_idx));
    }

    /// Remove a breakpoint.
    pub fn remove(&mut self, func_idx: usize, inst_idx: usize) -> bool {
        self.breakpoints.remove(&(func_idx, inst_idx))
    }

    /// Check if a breakpoint is set.
    pub fn is_set(&self, func_idx: usize, inst_idx: usize) -> bool {
        self.breakpoints.contains(&(func_idx, inst_idx))
    }

    /// Clear all breakpoints.
    pub fn clear(&mut self) {
        self.breakpoints.clear();
    }

    /// Get all breakpoints.
    pub fn get_all(&self) -> Vec<(usize, usize)> {
        self.breakpoints.iter().copied().collect()
    }

    /// Get number of breakpoints.
    pub fn count(&self) -> usize {
        self.breakpoints.len()
    }
}

impl Default for BreakpointManager {
    fn default() -> Self {
        Self::new()
    }
}
