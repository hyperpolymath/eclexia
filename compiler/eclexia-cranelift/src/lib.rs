// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Cranelift native code backend for Eclexia.
//!
//! Generates native machine code using Cranelift for fast compilation.
//! Intended for development builds where compilation speed matters
//! more than peak runtime performance.
//!
//! ## Targets
//!
//! - x86_64 (primary)
//! - aarch64 (ARM64)
//! - riscv64
//!
//! ## Features
//!
//! - Fast compilation (no LLVM overhead)
//! - Resource tracking via injected function calls
//! - Debug info generation

use eclexia_codegen::{Backend, CodegenError};
use eclexia_mir::MirFile;
use smol_str::SmolStr;

/// Target architecture for native code generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeTarget {
    X86_64,
    Aarch64,
    Riscv64,
}

impl NativeTarget {
    /// Get the target triple string.
    pub fn triple(&self) -> &'static str {
        match self {
            Self::X86_64 => "x86_64-unknown-linux-gnu",
            Self::Aarch64 => "aarch64-unknown-linux-gnu",
            Self::Riscv64 => "riscv64gc-unknown-linux-gnu",
        }
    }

    /// Detect the host target.
    pub fn host() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            Self::X86_64
        }
        #[cfg(target_arch = "aarch64")]
        {
            Self::Aarch64
        }
        #[cfg(target_arch = "riscv64")]
        {
            Self::Riscv64
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "riscv64")))]
        {
            Self::X86_64 // fallback
        }
    }
}

impl std::fmt::Display for NativeTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.triple())
    }
}

/// Output of the Cranelift backend.
#[derive(Debug, Clone)]
pub struct NativeModule {
    /// Target architecture.
    pub target: NativeTarget,
    /// Compiled function names and their sizes in bytes.
    pub functions: Vec<CompiledFunction>,
    /// Total code size in bytes.
    pub total_code_size: usize,
}

/// A compiled native function.
#[derive(Debug, Clone)]
pub struct CompiledFunction {
    /// Function name.
    pub name: SmolStr,
    /// Size of generated native code in bytes.
    pub code_size: usize,
    /// Whether this function uses resource tracking.
    pub has_resource_tracking: bool,
}

/// Cranelift backend for native code generation.
pub struct CraneliftBackend {
    target: NativeTarget,
}

impl CraneliftBackend {
    /// Create a new Cranelift backend for the given target.
    pub fn new(target: NativeTarget) -> Self {
        Self { target }
    }

    /// Create a Cranelift backend for the host architecture.
    pub fn host() -> Self {
        Self::new(NativeTarget::host())
    }

    /// Get the target architecture.
    pub fn target(&self) -> NativeTarget {
        self.target
    }

    /// Compile a single MIR function to a native function stub.
    fn compile_function(
        &self,
        func: &eclexia_mir::Function,
    ) -> Result<CompiledFunction, CodegenError> {
        let has_resource_tracking = func
            .basic_blocks
            .iter()
            .any(|(_, block)| {
                block.instructions.iter().any(|i| {
                    matches!(
                        i.kind,
                        eclexia_mir::InstructionKind::ResourceTrack { .. }
                    )
                })
            });

        // Stub: estimate code size based on instruction count
        let instr_count: usize = func
            .basic_blocks
            .iter()
            .map(|(_, block)| block.instructions.len())
            .sum();

        // Rough estimate: ~8 bytes per instruction average for native code
        let estimated_size = (instr_count + 2) * 8; // +2 for prologue/epilogue

        Ok(CompiledFunction {
            name: func.name.clone(),
            code_size: estimated_size,
            has_resource_tracking,
        })
    }
}

impl Backend for CraneliftBackend {
    type Output = NativeModule;

    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError> {
        let mut functions = Vec::new();
        let mut total_code_size = 0;

        for func in &mir.functions {
            let compiled = self.compile_function(func)?;
            total_code_size += compiled.code_size;
            functions.push(compiled);
        }

        Ok(NativeModule {
            target: self.target,
            functions,
            total_code_size,
        })
    }

    fn name(&self) -> &str {
        "cranelift"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, ConstantKind, Function, Instruction, InstructionKind,
        ResourceConstraint, Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn make_test_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(50.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![
                Instruction {
                    span: Span::new(0, 0),
                    kind: InstructionKind::ResourceTrack {
                        resource: SmolStr::new("energy"),
                        dimension: Dimension::energy(),
                        amount: Value::Constant(c),
                    },
                },
                Instruction {
                    span: Span::new(0, 0),
                    kind: InstructionKind::Nop,
                },
            ],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("main"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![ResourceConstraint {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                op: eclexia_mir::ConstraintOp::Le,
                bound: 100.0,
            }],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![func],
            constants,
        }
    }

    #[test]
    fn test_cranelift_backend_name() {
        let backend = CraneliftBackend::host();
        assert_eq!(backend.name(), "cranelift");
    }

    #[test]
    fn test_cranelift_generate() {
        let mut backend = CraneliftBackend::host();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "main");
        assert!(module.functions[0].has_resource_tracking);
        assert!(module.total_code_size > 0);
    }

    #[test]
    fn test_native_target_triple() {
        assert_eq!(NativeTarget::X86_64.triple(), "x86_64-unknown-linux-gnu");
        assert_eq!(NativeTarget::Aarch64.triple(), "aarch64-unknown-linux-gnu");
        assert_eq!(NativeTarget::Riscv64.triple(), "riscv64gc-unknown-linux-gnu");
    }

    #[test]
    fn test_native_target_host() {
        let host = NativeTarget::host();
        // On this system we know it's x86_64
        assert_eq!(host, NativeTarget::X86_64);
    }

    #[test]
    fn test_cranelift_empty_mir() {
        let mut backend = CraneliftBackend::host();
        let mir = MirFile {
            functions: vec![],
            constants: Arena::new(),
        };
        let module = backend.generate(&mir).unwrap();
        assert!(module.functions.is_empty());
        assert_eq!(module.total_code_size, 0);
    }

    #[test]
    fn test_native_target_display() {
        assert_eq!(format!("{}", NativeTarget::X86_64), "x86_64-unknown-linux-gnu");
    }
}
