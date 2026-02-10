// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Code generation for Eclexia.
//!
//! Transforms MIR into executable code via various backends:
//! - Bytecode: Portable stack-based VM
//! - Cranelift: JIT compilation
//! - LLVM: Optimized native code
//! - WebAssembly: Browser/WASI targets
//!
//! Key features:
//! - Resource tracking code emission
//! - Shadow price hook integration
//! - Adaptive function dispatch
//! - Efficient calling conventions

pub mod bytecode;
mod cranelift_backend;
mod vm;

pub use bytecode::{BytecodeGenerator, BytecodeModule, Instruction as BytecodeInstruction};
pub use cranelift_backend::CraneliftBackend;
pub use vm::{
    CallFrame, DebugAction, DebugEvent, ResourceUsage, Value as VmValue, VirtualMachine, VmError,
};

use eclexia_ast::types::Ty;
use eclexia_mir::{BlockId, LocalId, MirFile};
use smol_str::SmolStr;
use std::collections::HashMap;

/// Code generation backend trait
pub trait Backend {
    /// The output type (bytecode, object file, etc.)
    type Output;

    /// Generate code from MIR
    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError>;

    /// Get backend name
    fn name(&self) -> &str;
}

/// Code generation errors
#[derive(Debug, Clone)]
pub enum CodegenError {
    /// Unsupported feature
    UnsupportedFeature(String),

    /// Invalid instruction sequence
    InvalidInstruction(String),

    /// Missing function
    MissingFunction(SmolStr),

    /// Missing local variable
    MissingLocal(LocalId),

    /// Missing basic block
    MissingBlock(BlockId),

    /// Type error during codegen
    TypeError(String),

    /// Backend-specific error
    BackendError(String),
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenError::UnsupportedFeature(msg) => write!(f, "Unsupported feature: {}", msg),
            CodegenError::InvalidInstruction(msg) => write!(f, "Invalid instruction: {}", msg),
            CodegenError::MissingFunction(name) => write!(f, "Missing function: {}", name),
            CodegenError::MissingLocal(id) => write!(f, "Missing local variable: {}", id),
            CodegenError::MissingBlock(id) => write!(f, "Missing basic block: {:?}", id),
            CodegenError::TypeError(msg) => write!(f, "Type error: {}", msg),
            CodegenError::BackendError(msg) => write!(f, "Backend error: {}", msg),
        }
    }
}

impl std::error::Error for CodegenError {}

/// Common codegen utilities
pub struct CodegenContext {
    /// Function name to index mapping
    pub function_map: HashMap<SmolStr, usize>,

    /// String constant pool
    pub string_pool: Vec<String>,

    /// Float constant pool
    pub float_pool: Vec<f64>,

    /// Integer constant pool
    pub int_pool: Vec<i64>,
}

impl CodegenContext {
    /// Create a new empty codegen context.
    pub fn new() -> Self {
        Self {
            function_map: HashMap::new(),
            string_pool: Vec::new(),
            float_pool: Vec::new(),
            int_pool: Vec::new(),
        }
    }

    /// Get or insert a string constant
    pub fn intern_string(&mut self, s: &str) -> usize {
        if let Some(idx) = self.string_pool.iter().position(|x| x == s) {
            idx
        } else {
            let idx = self.string_pool.len();
            self.string_pool.push(s.to_string());
            idx
        }
    }

    /// Get or insert a float constant
    pub fn intern_float(&mut self, f: f64) -> usize {
        if let Some(idx) = self.float_pool.iter().position(|&x| x == f) {
            idx
        } else {
            let idx = self.float_pool.len();
            self.float_pool.push(f);
            idx
        }
    }

    /// Get or insert an integer constant
    pub fn intern_int(&mut self, i: i64) -> usize {
        if let Some(idx) = self.int_pool.iter().position(|&x| x == i) {
            idx
        } else {
            let idx = self.int_pool.len();
            self.int_pool.push(i);
            idx
        }
    }
}

impl Default for CodegenContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Type size calculation
pub fn size_of_type(ty: &Ty) -> usize {
    use eclexia_ast::types::PrimitiveTy;
    match ty {
        Ty::Primitive(prim) => match prim {
            PrimitiveTy::Unit => 0,
            PrimitiveTy::Bool => 1,
            PrimitiveTy::Char => 4,
            PrimitiveTy::I8 | PrimitiveTy::U8 => 1,
            PrimitiveTy::I16 | PrimitiveTy::U16 => 2,
            PrimitiveTy::I32 | PrimitiveTy::U32 | PrimitiveTy::F32 => 4,
            PrimitiveTy::I64 | PrimitiveTy::U64 | PrimitiveTy::F64 | PrimitiveTy::Float => 8,
            PrimitiveTy::I128 | PrimitiveTy::U128 => 16,
            PrimitiveTy::Int | PrimitiveTy::UInt => 8, // Platform-dependent, default to 64-bit
            PrimitiveTy::String => 8,                  // Pointer
        },
        Ty::Resource { base, .. } => size_of_type(&Ty::Primitive(*base)),
        Ty::Function { .. } => 8, // Function pointer
        Ty::Tuple(types) => types.iter().map(size_of_type).sum(),
        Ty::Array { elem, size } => {
            let elem_size = size_of_type(elem);
            size.map(|s| elem_size * s).unwrap_or(8) // Unknown size = pointer
        }
        Ty::Named { .. } => 8, // Placeholder for named types
        Ty::ForAll { body, .. } => size_of_type(body),
        Ty::Var(_) | Ty::Error | Ty::Never => 8, // Fallback
    }
}

/// Alignment calculation
pub fn align_of_type(ty: &Ty) -> usize {
    use eclexia_ast::types::PrimitiveTy;
    match ty {
        Ty::Primitive(prim) => match prim {
            PrimitiveTy::Unit => 1,
            PrimitiveTy::Bool => 1,
            PrimitiveTy::Char => 4,
            PrimitiveTy::I8 | PrimitiveTy::U8 => 1,
            PrimitiveTy::I16 | PrimitiveTy::U16 => 2,
            PrimitiveTy::I32 | PrimitiveTy::U32 | PrimitiveTy::F32 => 4,
            PrimitiveTy::I64 | PrimitiveTy::U64 | PrimitiveTy::F64 | PrimitiveTy::Float => 8,
            PrimitiveTy::I128 | PrimitiveTy::U128 => 16,
            PrimitiveTy::Int | PrimitiveTy::UInt => 8, // Platform-dependent
            PrimitiveTy::String => 8,
        },
        Ty::Resource { base, .. } => align_of_type(&Ty::Primitive(*base)),
        Ty::Function { .. } => 8,
        Ty::Tuple(types) => types.iter().map(align_of_type).max().unwrap_or(1),
        Ty::Array { elem, .. } => align_of_type(elem),
        Ty::Named { .. } => 8,
        Ty::ForAll { body, .. } => align_of_type(body),
        Ty::Var(_) | Ty::Error | Ty::Never => 8,
    }
}
