// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Bytecode generation backend.
//!
//! Generates portable stack-based bytecode for interpretation or JIT compilation.

use crate::{Backend, CodegenContext, CodegenError};
use eclexia_ast::dimension::Dimension;
use eclexia_ast::types::{Ty, PrimitiveTy};
use eclexia_mir::{
    MirFile, Function, Instruction as MirInstruction,
    InstructionKind, Terminator, Value, ConstantKind, BinaryOp, UnaryOp,
    LocalId, BlockId,
};
use smol_str::SmolStr;
use std::collections::HashMap;

/// Bytecode instruction
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Instruction {
    // Stack manipulation
    /// Push an integer constant onto the stack
    PushInt(i64),
    /// Push a float constant onto the stack
    PushFloat(f64),
    /// Push a boolean constant onto the stack
    PushBool(bool),
    /// Push a string constant onto the stack (index into string pool)
    PushString(usize),
    /// Push the unit value onto the stack
    PushUnit,

    /// Load local variable
    LoadLocal(u32),

    /// Store to local variable
    StoreLocal(u32),

    /// Duplicate top of stack
    Dup,

    /// Pop value from stack
    Pop,

    // Arithmetic
    /// Integer addition
    AddInt,
    /// Integer subtraction
    SubInt,
    /// Integer multiplication
    MulInt,
    /// Integer division
    DivInt,
    /// Integer remainder (modulo)
    RemInt,
    /// Integer negation
    NegInt,

    /// Float addition
    AddFloat,
    /// Float subtraction
    SubFloat,
    /// Float multiplication
    MulFloat,
    /// Float division
    DivFloat,
    /// Float negation
    NegFloat,

    // Comparison
    /// Integer equality comparison
    EqInt,
    /// Integer inequality comparison
    NeInt,
    /// Integer less-than comparison
    LtInt,
    /// Integer less-than-or-equal comparison
    LeInt,
    /// Integer greater-than comparison
    GtInt,
    /// Integer greater-than-or-equal comparison
    GeInt,

    /// Float equality comparison
    EqFloat,
    /// Float inequality comparison
    NeFloat,
    /// Float less-than comparison
    LtFloat,
    /// Float less-than-or-equal comparison
    LeFloat,
    /// Float greater-than comparison
    GtFloat,
    /// Float greater-than-or-equal comparison
    GeFloat,

    // Logical
    /// Logical AND of two booleans
    And,
    /// Logical OR of two booleans
    Or,
    /// Logical NOT of a boolean
    Not,

    // Bitwise
    /// Bitwise AND of two integers
    BitAnd,
    /// Bitwise OR of two integers
    BitOr,
    /// Bitwise XOR of two integers
    BitXor,
    /// Bitwise left shift
    Shl,
    /// Bitwise right shift
    Shr,
    /// Bitwise NOT (complement) of an integer
    BitNot,

    // Exponentiation
    /// Integer power (a ** b)
    PowInt,
    /// Float power (a ** b)
    PowFloat,

    // Range
    /// Create range (start..end)
    Range,
    /// Create inclusive range (start..=end)
    RangeInclusive,

    // Control flow
    /// Jump to label
    Jump(usize),

    /// Conditional jump (pops condition)
    JumpIf(usize),

    /// Conditional jump if false
    JumpIfNot(usize),

    /// Return from function
    Return,

    /// Return with value
    ReturnValue,

    // Function calls
    /// Call function by index
    Call(usize, u32), // (function_idx, arg_count)

    /// Call indirect (function on stack)
    CallIndirect(u32), // arg_count

    /// Push a function reference onto the stack
    PushFunction(usize), // function index

    /// Access a field on the top-of-stack value
    FieldAccess(SmolStr),

    /// Index into the top-of-stack value (index on top, base below)
    IndexAccess,

    // Resource tracking
    /// Track resource consumption
    TrackResource {
        resource: SmolStr,
        dimension: Dimension,
    },

    /// Shadow price hook
    ShadowPriceHook {
        resource: SmolStr,
        dimension: Dimension,
    },

    // Type operations
    /// Cast between types
    Cast { from: Ty, to: Ty },

    // Debugging
    /// Debug print top of stack
    DebugPrint,

    /// No operation
    Nop,
}

/// Bytecode module containing all compiled functions
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BytecodeModule {
    /// Functions in the module
    pub functions: Vec<BytecodeFunction>,

    /// String constant pool
    pub strings: Vec<String>,

    /// Float constant pool
    pub floats: Vec<f64>,

    /// Integer constant pool
    pub integers: Vec<i64>,

    /// Entry point function index
    pub entry_point: Option<usize>,
}

/// A compiled function
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BytecodeFunction {
    /// Function name
    pub name: SmolStr,

    /// Parameter count
    pub param_count: u32,

    /// Local variable count
    pub local_count: u32,

    /// Return type
    pub return_ty: Ty,

    /// Bytecode instructions
    pub instructions: Vec<Instruction>,

    /// Label to instruction index mapping
    pub labels: HashMap<SmolStr, usize>,

    /// Resource constraints
    pub resource_constraints: Vec<(SmolStr, Dimension, f64)>,

    /// Whether this is an adaptive function
    pub is_adaptive: bool,
}

/// Jump fixup entry
#[derive(Debug, Clone)]
struct JumpFixup {
    /// Instruction index to patch
    instruction_idx: usize,
    /// Target block ID
    target_block: BlockId,
}

/// Bytecode generator
pub struct BytecodeGenerator {
    /// Shared codegen context
    context: CodegenContext,

    /// Current function being compiled
    current_function: Option<BytecodeFunction>,

    /// Block to label mapping
    block_labels: HashMap<BlockId, SmolStr>,

    /// Local to stack slot mapping
    local_map: HashMap<LocalId, u32>,

    /// Jump fixups to resolve after block generation
    jump_fixups: Vec<JumpFixup>,

    /// Block ID to instruction index mapping
    block_positions: HashMap<BlockId, usize>,
}

impl BytecodeGenerator {
    /// Create a new bytecode generator with empty state.
    pub fn new() -> Self {
        Self {
            context: CodegenContext::new(),
            current_function: None,
            block_labels: HashMap::new(),
            local_map: HashMap::new(),
            jump_fixups: Vec::new(),
            block_positions: HashMap::new(),
        }
    }

    /// Generate bytecode for a function
    fn generate_function(&mut self, func: &Function, mir: &MirFile) -> Result<BytecodeFunction, CodegenError> {
        // Initialize function
        let mut bytecode_func = BytecodeFunction {
            name: func.name.clone(),
            param_count: func.params.len() as u32,
            local_count: (func.params.len() + func.locals.len()) as u32,
            return_ty: func.return_ty.clone(),
            instructions: Vec::new(),
            labels: HashMap::new(),
            resource_constraints: func.resource_constraints.iter()
                .map(|c| (c.resource.clone(), c.dimension, c.bound))
                .collect(),
            is_adaptive: func.is_adaptive,
        };

        self.current_function = Some(bytecode_func.clone());
        self.block_labels.clear();
        self.local_map.clear();
        self.jump_fixups.clear();
        self.block_positions.clear();

        // Map parameters to locals
        for (idx, param) in func.params.iter().enumerate() {
            self.local_map.insert(param.id, idx as u32);
        }

        // Map locals
        for (idx, local) in func.locals.iter().enumerate() {
            self.local_map.entry(local.id).or_insert_with(|| (func.params.len() + idx) as u32);
        }

        // Create labels for all blocks
        for (block_id, block) in func.basic_blocks.iter() {
            self.block_labels.insert(block_id, block.label.clone());
        }

        // Generate code for each basic block
        let mut instructions = Vec::new();
        for (block_id, block) in func.basic_blocks.iter() {
            // Record block position
            let block_pos = instructions.len();
            self.block_positions.insert(block_id, block_pos);
            bytecode_func.labels.insert(block.label.clone(), block_pos);

            // Generate instructions
            for inst in &block.instructions {
                self.generate_instruction(inst, &mut instructions, mir, func)?;
            }

            // Generate terminator
            self.generate_terminator(&block.terminator, &mut instructions, mir, func, block_id)?;
        }

        // Apply jump fixups
        for fixup in &self.jump_fixups {
            if let Some(&target_pos) = self.block_positions.get(&fixup.target_block) {
                match &mut instructions[fixup.instruction_idx] {
                    Instruction::Jump(ref mut target) => *target = target_pos,
                    Instruction::JumpIf(ref mut target) => *target = target_pos,
                    _ => {}
                }
            }
        }

        bytecode_func.instructions = instructions;
        Ok(bytecode_func)
    }

    /// Generate bytecode for a MIR instruction
    fn generate_instruction(
        &mut self,
        inst: &MirInstruction,
        out: &mut Vec<Instruction>,
        mir: &MirFile,
        mir_func: &Function,
    ) -> Result<(), CodegenError> {
        match &inst.kind {
            InstructionKind::Assign { target, value } => {
                // Evaluate value onto stack
                self.generate_value(value, out, mir, mir_func)?;
                // Store to local
                let local_idx = self.local_map.get(target)
                    .ok_or(CodegenError::MissingLocal(*target))?;
                out.push(Instruction::StoreLocal(*local_idx));
            }

            InstructionKind::Call { target, func, args, .. } => {
                // Push arguments onto stack
                for arg in args {
                    self.generate_value(arg, out, mir, mir_func)?;
                }

                // Call function
                match func {
                    Value::Constant(const_id) => {
                        if let ConstantKind::Function(name) = &mir.constants[*const_id].kind {
                            let func_idx = self.context.function_map.get(name)
                                .ok_or_else(|| CodegenError::MissingFunction(name.clone()))?;
                            out.push(Instruction::Call(*func_idx, args.len() as u32));
                        } else {
                            return Err(CodegenError::TypeError("Expected function constant".to_string()));
                        }
                    }
                    _ => {
                        // Indirect call
                        self.generate_value(func, out, mir, mir_func)?;
                        out.push(Instruction::CallIndirect(args.len() as u32));
                    }
                }

                // Store result if target specified
                if let Some(target) = target {
                    let local_idx = self.local_map.get(target)
                        .ok_or(CodegenError::MissingLocal(*target))?;
                    out.push(Instruction::StoreLocal(*local_idx));
                } else {
                    // Discard result
                    out.push(Instruction::Pop);
                }
            }

            InstructionKind::ResourceTrack { resource, dimension, amount } => {
                self.generate_value(amount, out, mir, mir_func)?;
                out.push(Instruction::TrackResource {
                    resource: resource.clone(),
                    dimension: *dimension,
                });
            }

            InstructionKind::ShadowPriceHook { resource, dimension } => {
                out.push(Instruction::ShadowPriceHook {
                    resource: resource.clone(),
                    dimension: *dimension,
                });
            }

            InstructionKind::Nop => {
                out.push(Instruction::Nop);
            }

            InstructionKind::Store { ptr: _, value } => {
                // Generate the value onto the stack, then emit a Nop since we
                // don't have memory addressing in the stack VM yet.
                self.generate_value(value, out, mir, mir_func)?;
                out.push(Instruction::Nop);
            }
        }

        Ok(())
    }

    /// Generate bytecode for a value
    fn generate_value(
        &mut self,
        value: &Value,
        out: &mut Vec<Instruction>,
        mir: &MirFile,
        mir_func: &Function,
    ) -> Result<(), CodegenError> {
        match value {
            Value::Local(local_id) => {
                let local_idx = self.local_map.get(local_id)
                    .ok_or(CodegenError::MissingLocal(*local_id))?;
                out.push(Instruction::LoadLocal(*local_idx));
            }

            Value::Constant(const_id) => {
                let constant = &mir.constants[*const_id];
                match &constant.kind {
                    ConstantKind::Int(i) => out.push(Instruction::PushInt(*i)),
                    ConstantKind::Float(f) => out.push(Instruction::PushFloat(*f)),
                    ConstantKind::Bool(b) => out.push(Instruction::PushBool(*b)),
                    ConstantKind::String(s) => {
                        let idx = self.context.intern_string(s);
                        out.push(Instruction::PushString(idx));
                    }
                    ConstantKind::Char(c) => out.push(Instruction::PushInt(*c as i64)),
                    ConstantKind::Unit => out.push(Instruction::PushUnit),
                    ConstantKind::Resource { value, .. } => out.push(Instruction::PushFloat(*value)),
                    ConstantKind::Function(name) => {
                        let func_idx = self.context.function_map.get(name)
                            .ok_or_else(|| CodegenError::MissingFunction(name.clone()))?;
                        out.push(Instruction::PushFunction(*func_idx));
                    }
                }
            }

            Value::Binary { op, lhs, rhs } => {
                self.generate_value(lhs, out, mir, mir_func)?;
                self.generate_value(rhs, out, mir, mir_func)?;
                self.generate_binary_op(*op, lhs, mir_func, mir, out)?;
            }

            Value::Unary { op, operand } => {
                self.generate_value(operand, out, mir, mir_func)?;
                self.generate_unary_op(*op, operand, mir_func, mir, out)?;
            }

            Value::Load { ptr } => {
                // Generate the pointer value onto the stack. In our stack-based
                // VM model, the value is already represented on the stack.
                self.generate_value(ptr, out, mir, mir_func)?;
            }

            Value::Field { base, field } => {
                self.generate_value(base, out, mir, mir_func)?;
                out.push(Instruction::FieldAccess(field.clone()));
            }

            Value::Index { base, index } => {
                self.generate_value(base, out, mir, mir_func)?;
                self.generate_value(index, out, mir, mir_func)?;
                out.push(Instruction::IndexAccess);
            }

            Value::Cast { value, target_ty } => {
                self.generate_value(value, out, mir, mir_func)?;
                // Determine source type from the value being cast
                let from_ty = self.get_value_type(value, mir_func, mir)
                    .unwrap_or(Ty::Primitive(PrimitiveTy::Int));
                out.push(Instruction::Cast {
                    from: from_ty,
                    to: target_ty.clone(),
                });
            }
        }

        Ok(())
    }

    /// Get the type of a value by inspecting constants and locals
    fn get_value_type(&self, value: &Value, mir_func: &Function, mir: &MirFile) -> Option<Ty> {
        match value {
            Value::Constant(c_id) => {
                let constant = &mir.constants[*c_id];
                Some(constant.ty.clone())
            }
            Value::Local(local_id) => {
                // Check params first
                for param in &mir_func.params {
                    if param.id == *local_id {
                        return Some(param.ty.clone());
                    }
                }
                // Check locals
                for local in &mir_func.locals {
                    if local.id == *local_id {
                        return Some(local.ty.clone());
                    }
                }
                None
            }
            Value::Binary { lhs, .. } => {
                // Binary operations return the type of their operands
                self.get_value_type(lhs, mir_func, mir)
            }
            _ => None,
        }
    }

    /// Generate binary operation (with type inference)
    fn generate_binary_op(&self, op: BinaryOp, lhs: &Value, mir_func: &Function, mir: &MirFile, out: &mut Vec<Instruction>) -> Result<(), CodegenError> {
        // Infer the type from the left operand
        let is_float = if let Some(ty) = self.get_value_type(lhs, mir_func, mir) {
            matches!(ty, Ty::Primitive(PrimitiveTy::Float))
        } else {
            false // Default to int if type unknown
        };

        let inst = match (op, is_float) {
            (BinaryOp::Add, false) => Instruction::AddInt,
            (BinaryOp::Add, true) => Instruction::AddFloat,
            (BinaryOp::Sub, false) => Instruction::SubInt,
            (BinaryOp::Sub, true) => Instruction::SubFloat,
            (BinaryOp::Mul, false) => Instruction::MulInt,
            (BinaryOp::Mul, true) => Instruction::MulFloat,
            (BinaryOp::Div, false) => Instruction::DivInt,
            (BinaryOp::Div, true) => Instruction::DivFloat,
            (BinaryOp::Rem, _) => Instruction::RemInt, // Remainder is int-only
            (BinaryOp::Pow, false) => Instruction::PowInt,
            (BinaryOp::Pow, true) => Instruction::PowFloat,
            (BinaryOp::Eq, false) => Instruction::EqInt,
            (BinaryOp::Eq, true) => Instruction::EqFloat,
            (BinaryOp::Ne, false) => Instruction::NeInt,
            (BinaryOp::Ne, true) => Instruction::NeFloat,
            (BinaryOp::Lt, false) => Instruction::LtInt,
            (BinaryOp::Lt, true) => Instruction::LtFloat,
            (BinaryOp::Le, false) => Instruction::LeInt,
            (BinaryOp::Le, true) => Instruction::LeFloat,
            (BinaryOp::Gt, false) => Instruction::GtInt,
            (BinaryOp::Gt, true) => Instruction::GtFloat,
            (BinaryOp::Ge, false) => Instruction::GeInt,
            (BinaryOp::Ge, true) => Instruction::GeFloat,
            (BinaryOp::And, _) => Instruction::And,
            (BinaryOp::Or, _) => Instruction::Or,
            (BinaryOp::BitAnd, _) => Instruction::BitAnd,
            (BinaryOp::BitOr, _) => Instruction::BitOr,
            (BinaryOp::BitXor, _) => Instruction::BitXor,
            (BinaryOp::Shl, _) => Instruction::Shl,
            (BinaryOp::Shr, _) => Instruction::Shr,
            (BinaryOp::Range, _) => Instruction::Range,
            (BinaryOp::RangeInclusive, _) => Instruction::RangeInclusive,
        };
        out.push(inst);
        Ok(())
    }

    /// Generate unary operation (with type inference)
    fn generate_unary_op(&self, op: UnaryOp, operand: &Value, mir_func: &Function, mir: &MirFile, out: &mut Vec<Instruction>) -> Result<(), CodegenError> {
        // Infer the type from the operand
        let is_float = if let Some(ty) = self.get_value_type(operand, mir_func, mir) {
            matches!(ty, Ty::Primitive(PrimitiveTy::Float))
        } else {
            false // Default to int if type unknown
        };

        let inst = match (op, is_float) {
            (UnaryOp::Neg, false) => Instruction::NegInt,
            (UnaryOp::Neg, true) => Instruction::NegFloat,
            (UnaryOp::Not, _) => Instruction::Not,
            (UnaryOp::BitNot, _) => Instruction::BitNot,
        };
        out.push(inst);
        Ok(())
    }

    /// Generate terminator
    fn generate_terminator(&mut self, term: &Terminator, out: &mut Vec<Instruction>, mir: &MirFile, mir_func: &Function, _current_block: BlockId) -> Result<(), CodegenError> {
        match term {
            Terminator::Return(value) => {
                if let Some(val) = value {
                    // Generate the return value onto the stack
                    self.generate_value(val, out, mir, mir_func)?;
                    out.push(Instruction::ReturnValue);
                } else {
                    out.push(Instruction::Return);
                }
            }

            Terminator::Goto(block_id) => {
                let instruction_idx = out.len();
                out.push(Instruction::Jump(0)); // Placeholder
                self.jump_fixups.push(JumpFixup {
                    instruction_idx,
                    target_block: *block_id,
                });
            }

            Terminator::Branch { condition, then_block, else_block } => {
                // Generate condition onto stack
                self.generate_value(condition, out, mir, mir_func)?;

                // JumpIf to then block
                let then_idx = out.len();
                out.push(Instruction::JumpIf(0)); // Placeholder
                self.jump_fixups.push(JumpFixup {
                    instruction_idx: then_idx,
                    target_block: *then_block,
                });

                // Unconditional jump to else block
                let else_idx = out.len();
                out.push(Instruction::Jump(0)); // Placeholder
                self.jump_fixups.push(JumpFixup {
                    instruction_idx: else_idx,
                    target_block: *else_block,
                });
            }

            Terminator::Switch { value, targets, default } => {
                // Generate the switch value onto the stack
                self.generate_value(value, out, mir, mir_func)?;

                // For each case target, emit: Dup, PushInt(case_value), EqInt, JumpIf(target)
                for (case_val, target_block) in targets {
                    out.push(Instruction::Dup);
                    out.push(Instruction::PushInt(*case_val));
                    out.push(Instruction::EqInt);
                    let jump_idx = out.len();
                    out.push(Instruction::JumpIf(0)); // Placeholder
                    self.jump_fixups.push(JumpFixup {
                        instruction_idx: jump_idx,
                        target_block: *target_block,
                    });
                }

                // Pop the remaining switch value and jump to default
                out.push(Instruction::Pop);
                let default_idx = out.len();
                out.push(Instruction::Jump(0)); // Placeholder
                self.jump_fixups.push(JumpFixup {
                    instruction_idx: default_idx,
                    target_block: *default,
                });
            }

            Terminator::Unreachable => {
                // No instruction needed
            }
        }

        Ok(())
    }
}

impl Backend for BytecodeGenerator {
    type Output = BytecodeModule;

    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError> {
        // Build function map
        for (idx, func) in mir.functions.iter().enumerate() {
            self.context.function_map.insert(func.name.clone(), idx);
        }

        // Generate bytecode for each function
        let mut functions = Vec::new();
        for func in &mir.functions {
            let bytecode_func = self.generate_function(func, mir)?;
            functions.push(bytecode_func);
        }

        Ok(BytecodeModule {
            functions,
            strings: self.context.string_pool.clone(),
            floats: self.context.float_pool.clone(),
            integers: self.context.int_pool.clone(),
            entry_point: self.context.function_map.get("main").copied(),
        })
    }

    fn name(&self) -> &str {
        "bytecode"
    }
}

impl Default for BytecodeGenerator {
    fn default() -> Self {
        Self::new()
    }
}

// ── .eclb bytecode file format ──────────────────────────────────────────────
//
// Header (8 bytes):
//   [0..4]  magic: b"ECLB"
//   [4]     format_version: u8 (currently 1)
//   [5]     encoding: u8 (0 = JSON)
//   [6..8]  reserved: [u8; 2]
// Payload:
//   JSON-encoded BytecodeModule

/// Magic bytes identifying an .eclb file.
pub const ECLB_MAGIC: &[u8; 4] = b"ECLB";

/// Current format version.
pub const ECLB_VERSION: u8 = 1;

/// Encoding type for the payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum EclbEncoding {
    Json = 0,
}

impl BytecodeModule {
    /// Write this module to an .eclb file.
    #[cfg(feature = "serde")]
    pub fn write_eclb(&self, path: &std::path::Path) -> Result<(), String> {
        let payload = serde_json::to_vec(self)
            .map_err(|e| format!("failed to serialize bytecode: {}", e))?;

        let mut out = Vec::with_capacity(8 + payload.len());
        out.extend_from_slice(ECLB_MAGIC);
        out.push(ECLB_VERSION);
        out.push(EclbEncoding::Json as u8);
        out.extend_from_slice(&[0u8; 2]); // reserved
        out.extend_from_slice(&payload);

        std::fs::write(path, &out)
            .map_err(|e| format!("failed to write {}: {}", path.display(), e))?;
        Ok(())
    }

    /// Read a BytecodeModule from an .eclb file.
    #[cfg(feature = "serde")]
    pub fn read_eclb(path: &std::path::Path) -> Result<Self, String> {
        let data = std::fs::read(path)
            .map_err(|e| format!("failed to read {}: {}", path.display(), e))?;

        if data.len() < 8 {
            return Err("file too small to be a valid .eclb".to_string());
        }

        if &data[0..4] != ECLB_MAGIC {
            return Err("not a valid .eclb file (bad magic)".to_string());
        }

        let version = data[4];
        if version != ECLB_VERSION {
            return Err(format!(
                "unsupported .eclb version {} (expected {})",
                version, ECLB_VERSION
            ));
        }

        let encoding = data[5];
        if encoding != EclbEncoding::Json as u8 {
            return Err(format!("unsupported .eclb encoding: {}", encoding));
        }

        let payload = &data[8..];
        serde_json::from_slice(payload)
            .map_err(|e| format!("failed to deserialize bytecode: {}", e))
    }

    /// Check if a file path looks like an .eclb bytecode file.
    pub fn is_eclb_path(path: &std::path::Path) -> bool {
        path.extension().and_then(|e| e.to_str()) == Some("eclb")
    }
}
