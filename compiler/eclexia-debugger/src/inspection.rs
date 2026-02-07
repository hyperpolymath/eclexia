// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! VM state inspection utilities.

use eclexia_codegen::VirtualMachine;

/// Inspector for VM state.
pub struct Inspector;

impl Inspector {
    /// Format stack for display.
    pub fn format_stack(vm: &VirtualMachine) -> String {
        let stack = vm.get_stack();
        if stack.is_empty() {
            return "Stack: (empty)".to_string();
        }

        let mut output = String::from("Stack:\n");
        for (i, value) in stack.iter().enumerate().rev() {
            output.push_str(&format!("  [{}] {:?}\n", i, value));
        }
        output
    }

    /// Format locals for display.
    pub fn format_locals(vm: &VirtualMachine) -> String {
        let locals = vm.get_locals();
        let call_stack = vm.get_call_stack();

        if call_stack.is_empty() {
            return "Locals: (no active frame)".to_string();
        }

        let frame = call_stack.last().unwrap();
        let module = vm.get_module();
        let func = &module.functions[frame.function_idx];

        let mut output = String::from("Locals:\n");
        for i in 0..func.local_count as usize {
            let local_idx = frame.bp + i;
            if local_idx < locals.len() {
                output.push_str(&format!("  [{}] {:?}\n", i, locals[local_idx]));
            }
        }
        output
    }

    /// Format call stack for display.
    pub fn format_call_stack(vm: &VirtualMachine) -> String {
        let call_stack = vm.get_call_stack();
        if call_stack.is_empty() {
            return "Call Stack: (empty)".to_string();
        }

        let module = vm.get_module();
        let mut output = String::from("Call Stack:\n");
        for (i, frame) in call_stack.iter().enumerate().rev() {
            let func = &module.functions[frame.function_idx];
            let name = if func.name.is_empty() {
                "<anonymous>"
            } else {
                func.name.as_str()
            };
            output.push_str(&format!(
                "  [{}] fn {} @ ip={}\n",
                i,
                name,
                frame.ip
            ));
        }
        output
    }

    /// Format resource usage for display.
    pub fn format_resources(vm: &VirtualMachine) -> String {
        let resources = vm.get_resources();
        if resources.is_empty() {
            return "Resources: (none tracked)".to_string();
        }

        let mut output = String::from("Resources:\n");
        for resource in resources {
            output.push_str(&format!(
                "  {} = {} {:?}\n",
                resource.resource, resource.amount, resource.dimension
            ));
        }
        output
    }

    /// Format current instruction for display.
    pub fn format_current_instruction(vm: &VirtualMachine) -> String {
        let call_stack = vm.get_call_stack();
        if call_stack.is_empty() {
            return "No active frame".to_string();
        }

        let frame = call_stack.last().unwrap();
        let module = vm.get_module();
        let func = &module.functions[frame.function_idx];

        if frame.ip >= func.instructions.len() {
            return format!("Invalid IP: {}", frame.ip);
        }

        let inst = &func.instructions[frame.ip];
        let name = if func.name.is_empty() {
            "<anonymous>"
        } else {
            func.name.as_str()
        };
        format!(
            "fn {} @ {}: {:?}",
            name,
            frame.ip,
            inst
        )
    }

    /// Get current position (function_idx, instruction_idx).
    pub fn get_current_position(vm: &VirtualMachine) -> Option<(usize, usize)> {
        vm.get_call_stack()
            .last()
            .map(|frame| (frame.function_idx, frame.ip))
    }
}
