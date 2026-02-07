// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Debug session management.

use crate::breakpoint::BreakpointManager;
use crate::inspection::Inspector;
use eclexia_codegen::VirtualMachine;

/// Debug session state.
pub struct DebugSession {
    /// The VM being debugged.
    vm: VirtualMachine,
    /// Breakpoint manager.
    breakpoints: BreakpointManager,
    /// Whether execution is paused.
    paused: bool,
}

impl DebugSession {
    /// Create a new debug session with the given VM.
    pub fn new(mut vm: VirtualMachine) -> Self {
        vm.enable_debug();

        Self {
            vm,
            breakpoints: BreakpointManager::new(),
            paused: false,
        }
    }

    /// Set a breakpoint at the given function and instruction.
    pub fn set_breakpoint(&mut self, func_idx: usize, inst_idx: usize) {
        self.breakpoints.set(func_idx, inst_idx);
        self.vm.set_breakpoint(func_idx, inst_idx);
    }

    /// Remove a breakpoint.
    pub fn remove_breakpoint(&mut self, func_idx: usize, inst_idx: usize) -> bool {
        self.vm.remove_breakpoint(func_idx, inst_idx);
        self.breakpoints.remove(func_idx, inst_idx)
    }

    /// Clear all breakpoints.
    pub fn clear_breakpoints(&mut self) {
        self.vm.clear_breakpoints();
        self.breakpoints.clear();
    }

    /// List all breakpoints.
    pub fn list_breakpoints(&self) -> Vec<(usize, usize)> {
        self.breakpoints.get_all()
    }

    /// Continue execution until next breakpoint.
    pub fn continue_execution(&mut self) -> Result<ContinueResult, String> {
        self.vm.disable_single_step();
        self.paused = false;

        // TODO: Implement actual execution
        // For now, return a placeholder
        Ok(ContinueResult::Breakpoint(0, 0))
    }

    /// Step to next instruction.
    pub fn step(&mut self) -> Result<(), String> {
        self.vm.enable_single_step();
        self.paused = false;

        // TODO: Implement actual single-step execution
        Ok(())
    }

    /// Get current instruction.
    pub fn get_current_instruction(&self) -> String {
        Inspector::format_current_instruction(&self.vm)
    }

    /// Inspect stack.
    pub fn inspect_stack(&self) -> String {
        Inspector::format_stack(&self.vm)
    }

    /// Inspect locals.
    pub fn inspect_locals(&self) -> String {
        Inspector::format_locals(&self.vm)
    }

    /// Inspect call stack.
    pub fn inspect_call_stack(&self) -> String {
        Inspector::format_call_stack(&self.vm)
    }

    /// Inspect resources.
    pub fn inspect_resources(&self) -> String {
        Inspector::format_resources(&self.vm)
    }

    /// Get current position.
    pub fn get_position(&self) -> Option<(usize, usize)> {
        Inspector::get_current_position(&self.vm)
    }

    /// Check if execution is paused.
    pub fn is_paused(&self) -> bool {
        self.paused
    }

    /// Get VM reference.
    pub fn vm(&self) -> &VirtualMachine {
        &self.vm
    }

    /// Get mutable VM reference.
    pub fn vm_mut(&mut self) -> &mut VirtualMachine {
        &mut self.vm
    }
}

/// Result of continuing execution.
#[derive(Debug, Clone)]
pub enum ContinueResult {
    /// Hit a breakpoint at (function_idx, instruction_idx).
    Breakpoint(usize, usize),
    /// Program finished with a value.
    Finished(String),
    /// Program errored.
    Error(String),
}
