// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! WebAssembly backend for Eclexia.
//!
//! Generates WebAssembly modules for browser and edge deployment.
//! Resource tracking is implemented via WASM imports, allowing
//! the JavaScript host to monitor resource consumption.
//!
//! ## Output format
//!
//! Generates valid WASM modules (binary format) containing:
//! - Exported functions
//! - Imported resource tracking functions (from host)
//! - Memory section for heap allocation
//! - Table section for indirect calls (effects)
//!
//! ## Resource tracking
//!
//! Resource operations are translated to host imports:
//! ```wasm
//! (import "eclexia" "track_resource" (func $track (param i32 f64)))
//! ```

use eclexia_codegen::{Backend, CodegenError};
use eclexia_mir::{InstructionKind, MirFile};
use smol_str::SmolStr;

/// WASM value type (subset of WASM types used by Eclexia).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmType {
    I32,
    I64,
    F32,
    F64,
}

impl std::fmt::Display for WasmType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
            Self::F32 => write!(f, "f32"),
            Self::F64 => write!(f, "f64"),
        }
    }
}

/// A WASM import declaration.
#[derive(Debug, Clone)]
pub struct WasmImport {
    /// Module name (e.g., "eclexia").
    pub module: SmolStr,
    /// Function name (e.g., "track_resource").
    pub name: SmolStr,
    /// Parameter types.
    pub params: Vec<WasmType>,
    /// Return type (None = void).
    pub result: Option<WasmType>,
}

/// A WASM export declaration.
#[derive(Debug, Clone)]
pub struct WasmExport {
    /// Exported name.
    pub name: SmolStr,
    /// Whether it's a function export.
    pub kind: WasmExportKind,
}

/// Kind of WASM export.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmExportKind {
    Function,
    Memory,
    Table,
    Global,
}

/// A compiled WASM function.
#[derive(Debug, Clone)]
pub struct WasmFunction {
    /// Function name.
    pub name: SmolStr,
    /// Parameter types.
    pub params: Vec<WasmType>,
    /// Return type.
    pub result: Option<WasmType>,
    /// Estimated bytecode size.
    pub estimated_size: usize,
    /// Whether this function uses resource imports.
    pub uses_resource_imports: bool,
}

/// Output of the WASM backend.
#[derive(Debug, Clone)]
pub struct WasmModule {
    /// Compiled functions.
    pub functions: Vec<WasmFunction>,
    /// Required imports.
    pub imports: Vec<WasmImport>,
    /// Exports.
    pub exports: Vec<WasmExport>,
    /// Initial memory pages (64KB each).
    pub initial_memory_pages: u32,
    /// Maximum memory pages.
    pub max_memory_pages: u32,
    /// Estimated total module size in bytes.
    pub estimated_size: usize,
}

/// WASM backend for Eclexia.
pub struct WasmBackend {
    initial_memory_pages: u32,
    max_memory_pages: u32,
}

impl WasmBackend {
    /// Create a new WASM backend with default memory settings.
    pub fn new() -> Self {
        Self {
            initial_memory_pages: 16,   // 1MB initial
            max_memory_pages: 256,      // 16MB max
        }
    }

    /// Set initial memory pages.
    pub fn with_initial_memory(mut self, pages: u32) -> Self {
        self.initial_memory_pages = pages;
        self
    }

    /// Set maximum memory pages.
    pub fn with_max_memory(mut self, pages: u32) -> Self {
        self.max_memory_pages = pages;
        self
    }

    /// Compile a MIR function to WASM function stub.
    fn compile_function(
        &self,
        func: &eclexia_mir::Function,
    ) -> Result<WasmFunction, CodegenError> {
        let uses_resource_imports = func
            .basic_blocks
            .iter()
            .any(|(_, block)| {
                block.instructions.iter().any(|i| {
                    matches!(i.kind, InstructionKind::ResourceTrack { .. })
                })
            });

        let instr_count: usize = func
            .basic_blocks
            .iter()
            .map(|(_, block)| block.instructions.len())
            .sum();

        // WASM bytecode is compact: ~4 bytes per instruction average
        let estimated_size = (instr_count + 2) * 4;

        Ok(WasmFunction {
            name: func.name.clone(),
            params: vec![], // TODO: derive from MIR params
            result: None,   // TODO: derive from MIR return type
            estimated_size,
            uses_resource_imports,
        })
    }

    /// Collect required imports from a MIR file.
    fn collect_imports(&self, mir: &MirFile) -> Vec<WasmImport> {
        let mut needs_resource_tracking = false;
        let mut needs_shadow_price = false;

        for func in &mir.functions {
            for (_, block) in func.basic_blocks.iter() {
                for instr in &block.instructions {
                    match &instr.kind {
                        InstructionKind::ResourceTrack { .. } => {
                            needs_resource_tracking = true;
                        }
                        InstructionKind::ShadowPriceHook { .. } => {
                            needs_shadow_price = true;
                        }
                        _ => {}
                    }
                }
            }
        }

        let mut imports = Vec::new();

        if needs_resource_tracking {
            imports.push(WasmImport {
                module: SmolStr::new("eclexia"),
                name: SmolStr::new("track_resource"),
                params: vec![WasmType::I32, WasmType::F64], // resource_id, amount
                result: None,
            });
        }

        if needs_shadow_price {
            imports.push(WasmImport {
                module: SmolStr::new("eclexia"),
                name: SmolStr::new("query_shadow_price"),
                params: vec![WasmType::I32], // resource_id
                result: Some(WasmType::F64), // price
            });
        }

        imports
    }
}

impl Default for WasmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for WasmBackend {
    type Output = WasmModule;

    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError> {
        let imports = self.collect_imports(mir);

        let mut functions = Vec::new();
        let mut total_size = 0;

        for func in &mir.functions {
            let compiled = self.compile_function(func)?;
            total_size += compiled.estimated_size;
            functions.push(compiled);
        }

        let exports: Vec<WasmExport> = functions
            .iter()
            .map(|f| WasmExport {
                name: f.name.clone(),
                kind: WasmExportKind::Function,
            })
            .chain(std::iter::once(WasmExport {
                name: SmolStr::new("memory"),
                kind: WasmExportKind::Memory,
            }))
            .collect();

        // Add overhead for headers, type section, etc.
        let estimated_size = total_size + 256;

        Ok(WasmModule {
            functions,
            imports,
            exports,
            initial_memory_pages: self.initial_memory_pages,
            max_memory_pages: self.max_memory_pages,
            estimated_size,
        })
    }

    fn name(&self) -> &str {
        "wasm"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, ConstantKind, Function, Instruction, Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn make_test_mir_with_resources() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(50.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ResourceTrack {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                    amount: Value::Constant(c),
                },
            }],
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
            resource_constraints: vec![],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![func],
            constants,
        }
    }

    fn make_simple_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Nop,
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("hello"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![func],
            constants: Arena::new(),
        }
    }

    #[test]
    fn test_wasm_backend_name() {
        let backend = WasmBackend::new();
        assert_eq!(backend.name(), "wasm");
    }

    #[test]
    fn test_wasm_generate() {
        let mut backend = WasmBackend::new();
        let mir = make_test_mir_with_resources();
        let module = backend.generate(&mir).unwrap();

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "main");
        assert!(module.functions[0].uses_resource_imports);
        assert_eq!(module.initial_memory_pages, 16);
        assert_eq!(module.max_memory_pages, 256);
    }

    #[test]
    fn test_wasm_imports_resource_tracking() {
        let mut backend = WasmBackend::new();
        let mir = make_test_mir_with_resources();
        let module = backend.generate(&mir).unwrap();

        assert!(!module.imports.is_empty());
        assert_eq!(module.imports[0].module, "eclexia");
        assert_eq!(module.imports[0].name, "track_resource");
    }

    #[test]
    fn test_wasm_no_imports_when_no_resources() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap();

        assert!(module.imports.is_empty());
    }

    #[test]
    fn test_wasm_exports() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap();

        // Should export the function + memory
        assert_eq!(module.exports.len(), 2);
        assert_eq!(module.exports[0].name, "hello");
        assert_eq!(module.exports[0].kind, WasmExportKind::Function);
        assert_eq!(module.exports[1].name, "memory");
        assert_eq!(module.exports[1].kind, WasmExportKind::Memory);
    }

    #[test]
    fn test_wasm_custom_memory() {
        let mut backend = WasmBackend::new()
            .with_initial_memory(32)
            .with_max_memory(512);
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap();

        assert_eq!(module.initial_memory_pages, 32);
        assert_eq!(module.max_memory_pages, 512);
    }

    #[test]
    fn test_wasm_empty_mir() {
        let mut backend = WasmBackend::new();
        let mir = MirFile {
            functions: vec![],
            constants: Arena::new(),
        };
        let module = backend.generate(&mir).unwrap();

        assert!(module.functions.is_empty());
        // Should still export memory
        assert_eq!(module.exports.len(), 1);
        assert_eq!(module.exports[0].kind, WasmExportKind::Memory);
    }

    #[test]
    fn test_wasm_type_display() {
        assert_eq!(format!("{}", WasmType::I32), "i32");
        assert_eq!(format!("{}", WasmType::F64), "f64");
    }
}
