// SPDX-License-Identifier: AGPL-3.0-or-later
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
pub enum Instruction {
    // Stack manipulation
    /// Push constant onto stack
    PushInt(i64),
    PushFloat(f64),
    PushBool(bool),
    PushString(usize), // Index into string pool
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
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    RemInt,
    NegInt,

    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,

    // Comparison
    EqInt,
    NeInt,
    LtInt,
    LeInt,
    GtInt,
    GeInt,

    EqFloat,
    NeFloat,
    LtFloat,
    LeFloat,
    GtFloat,
    GeFloat,

    // Logical
    And,
    Or,
    Not,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    BitNot,

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
            if !self.local_map.contains_key(&local.id) {
                self.local_map.insert(local.id, (func.params.len() + idx) as u32);
            }
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
        &self,
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
                    .ok_or_else(|| CodegenError::MissingLocal(*target))?;
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
                        .ok_or_else(|| CodegenError::MissingLocal(*target))?;
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

            InstructionKind::Store { .. } => {
                return Err(CodegenError::UnsupportedFeature("Store instruction".to_string()));
            }
        }

        Ok(())
    }

    /// Generate bytecode for a value
    fn generate_value(
        &self,
        value: &Value,
        out: &mut Vec<Instruction>,
        mir: &MirFile,
        mir_func: &Function,
    ) -> Result<(), CodegenError> {
        match value {
            Value::Local(local_id) => {
                let local_idx = self.local_map.get(local_id)
                    .ok_or_else(|| CodegenError::MissingLocal(*local_id))?;
                out.push(Instruction::LoadLocal(*local_idx));
            }

            Value::Constant(const_id) => {
                let constant = &mir.constants[*const_id];
                match &constant.kind {
                    ConstantKind::Int(i) => out.push(Instruction::PushInt(*i)),
                    ConstantKind::Float(f) => out.push(Instruction::PushFloat(*f)),
                    ConstantKind::Bool(b) => out.push(Instruction::PushBool(*b)),
                    ConstantKind::String(_s) => {
                        // This is a read-only borrow, we can't mutate context here
                        // We'll need to handle this differently
                        out.push(Instruction::PushString(0)); // Placeholder
                    }
                    ConstantKind::Char(c) => out.push(Instruction::PushInt(*c as i64)),
                    ConstantKind::Unit => out.push(Instruction::PushUnit),
                    ConstantKind::Resource { value, .. } => out.push(Instruction::PushFloat(*value)),
                    ConstantKind::Function(_) => {
                        return Err(CodegenError::UnsupportedFeature("Function constant as value".to_string()));
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

            Value::Load { ptr: _ } => {
                return Err(CodegenError::UnsupportedFeature("Load instruction".to_string()));
            }

            Value::Field { .. } | Value::Index { .. } => {
                return Err(CodegenError::UnsupportedFeature("Field/Index access".to_string()));
            }

            Value::Cast { value, target_ty } => {
                self.generate_value(value, out, mir, mir_func)?;
                // Determine source type (would need type inference here)
                out.push(Instruction::Cast {
                    from: Ty::Primitive(PrimitiveTy::Int), // Placeholder
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

            Terminator::Switch { .. } => {
                return Err(CodegenError::UnsupportedFeature("Switch terminator".to_string()));
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
