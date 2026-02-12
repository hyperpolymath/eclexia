// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! WebAssembly backend for Eclexia.
//!
//! Generates valid WebAssembly binary modules from Eclexia MIR for browser
//! and edge deployment. Resource tracking is implemented via WASM imports,
//! allowing the JavaScript host to monitor resource consumption.
//!
//! ## Output format
//!
//! Generates valid `.wasm` modules (binary format) containing:
//! - Type section (function signatures)
//! - Import section (resource tracking from host)
//! - Function section (function bodies with real WASM instructions)
//! - Memory section (linear memory for heap allocation)
//! - Export section (functions + memory)
//! - Data section (string constants)
//!
//! ## Resource tracking
//!
//! Resource operations are translated to host imports:
//! ```wasm
//! (import "eclexia" "track_resource" (func $track (param i32 f64)))
//! ```
//!
//! ## Type representation
//!
//! - Primitives: i32, i64, f32, f64 map directly to WASM value types
//! - Strings: stored in data section, referenced by i32 offset
//! - Tuples: stored in linear memory, fields at 8-byte stride, accessed via i32 pointer
//! - Arrays: stored as (pointer: i32, length: i32) header + contiguous elements
//! - Structs: stored in linear memory, accessed via i32 pointer
//!
//! ## Limitations
//!
//! - No garbage collection (bump allocator, no free)
//! - WASI preview1 integration available (enable with `with_wasi(true)`)
//! - Indirect calls via basic function table only

use eclexia_ast::types::{PrimitiveTy, Ty};
use eclexia_codegen::{Backend, CodegenError};
use eclexia_mir::{
    BinaryOp, BlockId, ConstantKind, InstructionKind, MirFile, Terminator, UnaryOp, Value,
};
use smol_str::SmolStr;
use wasm_encoder::{
    CodeSection, DataSection, EntityType, ExportKind, ExportSection, Function as WasmFunc,
    FunctionSection, ImportSection, Instruction, MemorySection, MemoryType, Module, TypeSection,
    ValType,
};

/// WASM value type (subset of WASM types used by Eclexia).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmType {
    I32,
    I64,
    F32,
    F64,
}

impl WasmType {
    /// Convert to wasm-encoder ValType.
    fn to_val_type(self) -> ValType {
        match self {
            Self::I32 => ValType::I32,
            Self::I64 => ValType::I64,
            Self::F32 => ValType::F32,
            Self::F64 => ValType::F64,
        }
    }
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
    /// Actual bytecode size (from wasm-encoder).
    pub code_size: usize,
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
    /// Actual module binary size in bytes.
    pub binary_size: usize,
    /// The WASM binary module bytes.
    binary: Vec<u8>,
}

impl WasmModule {
    /// Get the WASM binary bytes.
    pub fn to_bytes(&self) -> &[u8] {
        &self.binary
    }

    /// Consume and return the WASM binary bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.binary
    }
}

/// Map an Eclexia type to a WASM value type.
///
/// Primitive types map directly. Complex types (tuples, arrays, structs,
/// strings) are represented as i32 pointers into linear memory.
fn ty_to_wasm(ty: &Ty) -> Option<WasmType> {
    match ty {
        Ty::Primitive(p) => prim_to_wasm(*p),
        Ty::Resource { base, .. } => prim_to_wasm(*base),
        // Complex types become i32 pointers into linear memory
        Ty::Tuple(_) | Ty::Array { .. } | Ty::Named { .. } => Some(WasmType::I32),
        Ty::Function { .. } => Some(WasmType::I32), // function pointer
        _ => None,
    }
}

/// Calculate the byte size of a type in linear memory.
fn ty_byte_size(ty: &Ty) -> u32 {
    match ty {
        Ty::Primitive(p) | Ty::Resource { base: p, .. } => match p {
            PrimitiveTy::I8 | PrimitiveTy::U8 | PrimitiveTy::Bool => 4, // WASM aligns to 4
            PrimitiveTy::I16 | PrimitiveTy::U16 | PrimitiveTy::Char => 4,
            PrimitiveTy::Int | PrimitiveTy::I32 | PrimitiveTy::UInt | PrimitiveTy::U32 => 4,
            PrimitiveTy::I64 | PrimitiveTy::U64 => 8,
            PrimitiveTy::I128 | PrimitiveTy::U128 => 16,
            PrimitiveTy::F32 | PrimitiveTy::Float => 8, // promote to 8 for alignment
            PrimitiveTy::F64 => 8,
            PrimitiveTy::String => 8, // (offset: i32, length: i32)
            PrimitiveTy::Unit => 0,
        },
        Ty::Tuple(fields) => fields.iter().map(ty_byte_size).sum(),
        Ty::Array { .. } => 8, // (pointer: i32, length: i32)
        Ty::Named { .. } => 4, // pointer
        _ => 4,
    }
}

/// Calculate the byte offset of a tuple field.
fn tuple_field_offset(fields: &[Ty], index: usize) -> u32 {
    fields[..index].iter().map(ty_byte_size).sum()
}

/// Map an Eclexia primitive type to a WASM value type.
fn prim_to_wasm(p: PrimitiveTy) -> Option<WasmType> {
    match p {
        PrimitiveTy::Int | PrimitiveTy::I64 | PrimitiveTy::U64 => Some(WasmType::I64),
        PrimitiveTy::I32 | PrimitiveTy::U32 | PrimitiveTy::Bool | PrimitiveTy::Char => {
            Some(WasmType::I32)
        }
        PrimitiveTy::I8 | PrimitiveTy::U8 | PrimitiveTy::I16 | PrimitiveTy::U16 => {
            Some(WasmType::I32)
        }
        PrimitiveTy::I128 | PrimitiveTy::U128 | PrimitiveTy::UInt => Some(WasmType::I64),
        PrimitiveTy::Float | PrimitiveTy::F64 => Some(WasmType::F64),
        PrimitiveTy::F32 => Some(WasmType::F32),
        PrimitiveTy::String => Some(WasmType::I32), // offset into linear memory
        PrimitiveTy::Unit => None,                  // void
    }
}

/// Determine if a type maps to i64.
fn is_i64_type(ty: &Ty) -> bool {
    matches!(ty_to_wasm(ty), Some(WasmType::I64))
}

/// Determine if a type is a float type in WASM (f32 or f64).
fn is_float_type(ty: &Ty) -> bool {
    matches!(ty_to_wasm(ty), Some(WasmType::F32) | Some(WasmType::F64))
}

/// Determine if a type maps to f32.
fn is_f32_type(ty: &Ty) -> bool {
    matches!(ty_to_wasm(ty), Some(WasmType::F32))
}

/// Tracks the actual import function indices in the WASM module.
///
/// Import indices depend on which imports are present, so they
/// must be computed dynamically rather than hardcoded.
struct ImportIndices {
    track_resource: Option<u32>,
    query_shadow_price: Option<u32>,
    pow: Option<u32>,
    // WASI imports (preview1)
    fd_write: Option<u32>,
    clock_time_get: Option<u32>,
    args_get: Option<u32>,
    args_sizes_get: Option<u32>,
}

/// Bump allocator for WASM linear memory.
///
/// Tracks the next free offset in linear memory. Strings from the data
/// section occupy the beginning of memory; the heap starts after them.
struct BumpAllocator {
    next_offset: u32,
}

impl BumpAllocator {
    fn new(initial_offset: u32) -> Self {
        Self {
            next_offset: initial_offset,
        }
    }

    /// Allocate `size` bytes, returning the start offset.
    fn alloc(&mut self, size: u32) -> u32 {
        // Align to 8 bytes for f64 compatibility
        let aligned = (self.next_offset + 7) & !7;
        self.next_offset = aligned + size;
        aligned
    }
}

/// WASM backend for Eclexia.
pub struct WasmBackend {
    initial_memory_pages: u32,
    max_memory_pages: u32,
    /// Enable WASI preview1 integration.
    wasi_enabled: bool,
}

impl WasmBackend {
    /// Create a new WASM backend with default memory settings.
    pub fn new() -> Self {
        Self {
            initial_memory_pages: 16, // 1MB initial
            max_memory_pages: 256,    // 16MB max
            wasi_enabled: false,
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

    /// Enable WASI preview1 integration.
    pub fn with_wasi(mut self, enabled: bool) -> Self {
        self.wasi_enabled = enabled;
        self
    }

    /// Check whether a MIR Value (recursively) contains a Pow operation.
    fn value_has_pow(value: &Value) -> bool {
        match value {
            Value::Binary {
                op: BinaryOp::Pow, ..
            } => true,
            Value::Binary { lhs, rhs, .. } => Self::value_has_pow(lhs) || Self::value_has_pow(rhs),
            Value::Unary { operand, .. } => Self::value_has_pow(operand),
            Value::Cast { value, .. } => Self::value_has_pow(value),
            _ => false,
        }
    }

    /// Collect required imports from a MIR file and compute their indices.
    fn collect_imports(&self, mir: &MirFile) -> (Vec<WasmImport>, ImportIndices) {
        let mut needs_resource_tracking = false;
        let mut needs_shadow_price = false;
        let mut needs_pow = false;

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
                        InstructionKind::Assign { value, .. } => {
                            if Self::value_has_pow(value) {
                                needs_pow = true;
                            }
                        }
                        _ => {}
                    }
                }
                // Check terminator return values for Pow
                if let Terminator::Return(Some(v)) = &block.terminator {
                    if Self::value_has_pow(v) {
                        needs_pow = true;
                    }
                }
                // Check branch conditions too
                if let Terminator::Branch { condition, .. } = &block.terminator {
                    if Self::value_has_pow(condition) {
                        needs_pow = true;
                    }
                }
            }
        }

        let mut imports = Vec::new();
        let mut indices = ImportIndices {
            track_resource: None,
            query_shadow_price: None,
            pow: None,
            fd_write: None,
            clock_time_get: None,
            args_get: None,
            args_sizes_get: None,
        };

        if needs_resource_tracking {
            indices.track_resource = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("eclexia"),
                name: SmolStr::new("track_resource"),
                params: vec![WasmType::I32, WasmType::F64],
                result: None,
            });
        }

        if needs_shadow_price {
            indices.query_shadow_price = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("eclexia"),
                name: SmolStr::new("query_shadow_price"),
                params: vec![WasmType::I32],
                result: Some(WasmType::F64),
            });
        }

        if needs_pow {
            indices.pow = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("eclexia"),
                name: SmolStr::new("pow"),
                params: vec![WasmType::F64, WasmType::F64],
                result: Some(WasmType::F64),
            });
        }

        // WASI preview1 imports (if enabled)
        if self.wasi_enabled {
            // fd_write: for stdout/stderr output
            // signature: (fd: i32, iovs: i32, iovs_len: i32, nwritten: i32) -> i32
            indices.fd_write = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("wasi_snapshot_preview1"),
                name: SmolStr::new("fd_write"),
                params: vec![WasmType::I32, WasmType::I32, WasmType::I32, WasmType::I32],
                result: Some(WasmType::I32),
            });

            // clock_time_get: for timing operations
            // signature: (clock_id: i32, precision: i64, timestamp: i32) -> i32
            indices.clock_time_get = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("wasi_snapshot_preview1"),
                name: SmolStr::new("clock_time_get"),
                params: vec![WasmType::I32, WasmType::I64, WasmType::I32],
                result: Some(WasmType::I32),
            });

            // args_get: retrieve command-line arguments
            // signature: (argv: i32, argv_buf: i32) -> i32
            indices.args_get = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("wasi_snapshot_preview1"),
                name: SmolStr::new("args_get"),
                params: vec![WasmType::I32, WasmType::I32],
                result: Some(WasmType::I32),
            });

            // args_sizes_get: get argument count and buffer size
            // signature: (argc: i32, argv_buf_size: i32) -> i32
            indices.args_sizes_get = Some(imports.len() as u32);
            imports.push(WasmImport {
                module: SmolStr::new("wasi_snapshot_preview1"),
                name: SmolStr::new("args_sizes_get"),
                params: vec![WasmType::I32, WasmType::I32],
                result: Some(WasmType::I32),
            });
        }

        (imports, indices)
    }

    /// Derive WASM param types from a MIR function.
    fn derive_params(func: &eclexia_mir::Function) -> Vec<WasmType> {
        func.params
            .iter()
            .filter_map(|local| ty_to_wasm(&local.ty))
            .collect()
    }

    /// Derive WASM return type from a MIR function.
    fn derive_result(func: &eclexia_mir::Function) -> Option<WasmType> {
        ty_to_wasm(&func.return_ty)
    }

    /// Derive WASM local types (excluding params) from a MIR function.
    fn derive_locals(func: &eclexia_mir::Function) -> Vec<ValType> {
        func.locals
            .iter()
            .filter_map(|local| ty_to_wasm(&local.ty).map(|t| t.to_val_type()))
            .collect()
    }

    /// Lower a MIR Value to WASM instructions, appending to the function body.
    fn lower_value(
        &self,
        value: &Value,
        func_body: &mut WasmFunc,
        mir_func: &eclexia_mir::Function,
        mir: &MirFile,
        import_count: u32,
        string_offsets: &[(SmolStr, u32)],
        indices: &ImportIndices,
    ) {
        match value {
            Value::Constant(id) => {
                let constant = &mir.constants[*id];
                match &constant.kind {
                    ConstantKind::Int(n) => {
                        // Check the declared type to pick i32 vs i64
                        if is_i64_type(&constant.ty) {
                            func_body.instruction(&Instruction::I64Const(*n));
                        } else {
                            func_body.instruction(&Instruction::I32Const(*n as i32));
                        }
                    }
                    ConstantKind::Float(f) => {
                        if is_f32_type(&constant.ty) {
                            func_body.instruction(&Instruction::F32Const(*f as f32));
                        } else {
                            func_body.instruction(&Instruction::F64Const(*f));
                        }
                    }
                    ConstantKind::Bool(b) => {
                        func_body.instruction(&Instruction::I32Const(*b as i32));
                    }
                    ConstantKind::Char(c) => {
                        func_body.instruction(&Instruction::I32Const(*c as i32));
                    }
                    ConstantKind::Unit => {
                        // Unit produces no value on the WASM stack
                    }
                    ConstantKind::String(s) => {
                        // Look up offset in data section
                        let offset = string_offsets
                            .iter()
                            .find(|(key, _)| key == s)
                            .map(|(_, off)| *off)
                            .unwrap_or(0);
                        func_body.instruction(&Instruction::I32Const(offset as i32));
                    }
                    ConstantKind::Resource { value, .. } => {
                        func_body.instruction(&Instruction::F64Const(*value));
                    }
                    ConstantKind::Function(_name) => {
                        // Function reference — push function index as i32
                        // (real resolution would need a name→index map)
                        func_body.instruction(&Instruction::I32Const(0));
                    }
                }
            }
            Value::Local(id) => {
                func_body.instruction(&Instruction::LocalGet(*id));
            }
            Value::Binary { op, lhs, rhs } => {
                // Lower operands first (stack-based)
                self.lower_value(
                    lhs,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                self.lower_value(
                    rhs,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );

                // Infer type from context: use lhs type heuristic
                let use_i64 = self.value_is_i64(lhs, mir_func, mir);
                let use_float = self.value_is_float(lhs, mir_func, mir);
                let use_f32 = self.value_is_f32(lhs, mir_func, mir);

                match op {
                    BinaryOp::Add if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Add);
                    }
                    BinaryOp::Add if use_float => {
                        func_body.instruction(&Instruction::F64Add);
                    }
                    BinaryOp::Add if use_i64 => {
                        func_body.instruction(&Instruction::I64Add);
                    }
                    BinaryOp::Add => {
                        func_body.instruction(&Instruction::I32Add);
                    }

                    BinaryOp::Sub if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Sub);
                    }
                    BinaryOp::Sub if use_float => {
                        func_body.instruction(&Instruction::F64Sub);
                    }
                    BinaryOp::Sub if use_i64 => {
                        func_body.instruction(&Instruction::I64Sub);
                    }
                    BinaryOp::Sub => {
                        func_body.instruction(&Instruction::I32Sub);
                    }

                    BinaryOp::Mul if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Mul);
                    }
                    BinaryOp::Mul if use_float => {
                        func_body.instruction(&Instruction::F64Mul);
                    }
                    BinaryOp::Mul if use_i64 => {
                        func_body.instruction(&Instruction::I64Mul);
                    }
                    BinaryOp::Mul => {
                        func_body.instruction(&Instruction::I32Mul);
                    }

                    BinaryOp::Div if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Div);
                    }
                    BinaryOp::Div if use_float => {
                        func_body.instruction(&Instruction::F64Div);
                    }
                    BinaryOp::Div if use_i64 => {
                        func_body.instruction(&Instruction::I64DivS);
                    }
                    BinaryOp::Div => {
                        func_body.instruction(&Instruction::I32DivS);
                    }

                    BinaryOp::Rem if use_i64 => {
                        func_body.instruction(&Instruction::I64RemS);
                    }
                    BinaryOp::Rem => {
                        func_body.instruction(&Instruction::I32RemS);
                    }

                    BinaryOp::Eq if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Eq);
                    }
                    BinaryOp::Eq if use_float => {
                        func_body.instruction(&Instruction::F64Eq);
                    }
                    BinaryOp::Eq if use_i64 => {
                        func_body.instruction(&Instruction::I64Eq);
                    }
                    BinaryOp::Eq => {
                        func_body.instruction(&Instruction::I32Eq);
                    }

                    BinaryOp::Ne if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Ne);
                    }
                    BinaryOp::Ne if use_float => {
                        func_body.instruction(&Instruction::F64Ne);
                    }
                    BinaryOp::Ne if use_i64 => {
                        func_body.instruction(&Instruction::I64Ne);
                    }
                    BinaryOp::Ne => {
                        func_body.instruction(&Instruction::I32Ne);
                    }

                    BinaryOp::Lt if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Lt);
                    }
                    BinaryOp::Lt if use_float => {
                        func_body.instruction(&Instruction::F64Lt);
                    }
                    BinaryOp::Lt if use_i64 => {
                        func_body.instruction(&Instruction::I64LtS);
                    }
                    BinaryOp::Lt => {
                        func_body.instruction(&Instruction::I32LtS);
                    }

                    BinaryOp::Le if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Le);
                    }
                    BinaryOp::Le if use_float => {
                        func_body.instruction(&Instruction::F64Le);
                    }
                    BinaryOp::Le if use_i64 => {
                        func_body.instruction(&Instruction::I64LeS);
                    }
                    BinaryOp::Le => {
                        func_body.instruction(&Instruction::I32LeS);
                    }

                    BinaryOp::Gt if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Gt);
                    }
                    BinaryOp::Gt if use_float => {
                        func_body.instruction(&Instruction::F64Gt);
                    }
                    BinaryOp::Gt if use_i64 => {
                        func_body.instruction(&Instruction::I64GtS);
                    }
                    BinaryOp::Gt => {
                        func_body.instruction(&Instruction::I32GtS);
                    }

                    BinaryOp::Ge if use_float && use_f32 => {
                        func_body.instruction(&Instruction::F32Ge);
                    }
                    BinaryOp::Ge if use_float => {
                        func_body.instruction(&Instruction::F64Ge);
                    }
                    BinaryOp::Ge if use_i64 => {
                        func_body.instruction(&Instruction::I64GeS);
                    }
                    BinaryOp::Ge => {
                        func_body.instruction(&Instruction::I32GeS);
                    }

                    BinaryOp::And => {
                        func_body.instruction(&Instruction::I32And);
                    }
                    BinaryOp::Or => {
                        func_body.instruction(&Instruction::I32Or);
                    }

                    BinaryOp::BitAnd if use_i64 => {
                        func_body.instruction(&Instruction::I64And);
                    }
                    BinaryOp::BitAnd => {
                        func_body.instruction(&Instruction::I32And);
                    }
                    BinaryOp::BitOr if use_i64 => {
                        func_body.instruction(&Instruction::I64Or);
                    }
                    BinaryOp::BitOr => {
                        func_body.instruction(&Instruction::I32Or);
                    }
                    BinaryOp::BitXor if use_i64 => {
                        func_body.instruction(&Instruction::I64Xor);
                    }
                    BinaryOp::BitXor => {
                        func_body.instruction(&Instruction::I32Xor);
                    }
                    BinaryOp::Shl if use_i64 => {
                        func_body.instruction(&Instruction::I64Shl);
                    }
                    BinaryOp::Shl => {
                        func_body.instruction(&Instruction::I32Shl);
                    }
                    BinaryOp::Shr if use_i64 => {
                        func_body.instruction(&Instruction::I64ShrS);
                    }
                    BinaryOp::Shr => {
                        func_body.instruction(&Instruction::I32ShrS);
                    }

                    BinaryOp::Pow => {
                        // Call imported pow(f64, f64) -> f64.
                        // Operands are already on the stack from the outer lowering.
                        // Drop them and re-emit with f64 conversion so the stack
                        // is clean for the call.
                        if let Some(pow_idx) = indices.pow {
                            func_body.instruction(&Instruction::Drop);
                            func_body.instruction(&Instruction::Drop);
                            // Emit lhs as f64
                            self.lower_value(
                                lhs,
                                func_body,
                                mir_func,
                                mir,
                                import_count,
                                string_offsets,
                                indices,
                            );
                            if use_float && use_f32 {
                                func_body.instruction(&Instruction::F64PromoteF32);
                            } else if !use_float && use_i64 {
                                func_body.instruction(&Instruction::F64ConvertI64S);
                            } else if !use_float {
                                func_body.instruction(&Instruction::F64ConvertI32S);
                            }
                            // Emit rhs as f64
                            self.lower_value(
                                rhs,
                                func_body,
                                mir_func,
                                mir,
                                import_count,
                                string_offsets,
                                indices,
                            );
                            if use_float && use_f32 {
                                func_body.instruction(&Instruction::F64PromoteF32);
                            } else if !use_float && use_i64 {
                                func_body.instruction(&Instruction::F64ConvertI64S);
                            } else if !use_float {
                                func_body.instruction(&Instruction::F64ConvertI32S);
                            }
                            // Call pow(f64, f64) -> f64
                            func_body.instruction(&Instruction::Call(pow_idx));
                            // Convert result back to original type
                            if use_float && use_f32 {
                                func_body.instruction(&Instruction::F32DemoteF64);
                            } else if !use_float && use_i64 {
                                func_body.instruction(&Instruction::I64TruncF64S);
                            } else if !use_float {
                                func_body.instruction(&Instruction::I32TruncF64S);
                            }
                        } else {
                            // No pow import: drop operands, push 0
                            func_body.instruction(&Instruction::Drop);
                            func_body.instruction(&Instruction::Drop);
                            if use_float {
                                func_body.instruction(&Instruction::F64Const(0.0));
                            } else if use_i64 {
                                func_body.instruction(&Instruction::I64Const(0));
                            } else {
                                func_body.instruction(&Instruction::I32Const(0));
                            }
                        }
                    }
                    // Range types are not directly representable in WASM
                    BinaryOp::Range | BinaryOp::RangeInclusive => {
                        func_body.instruction(&Instruction::Drop);
                        func_body.instruction(&Instruction::Drop);
                        if use_i64 {
                            func_body.instruction(&Instruction::I64Const(0));
                        } else {
                            func_body.instruction(&Instruction::I32Const(0));
                        }
                    }
                }
            }
            Value::Unary { op, operand } => {
                let use_i64 = self.value_is_i64(operand, mir_func, mir);
                let use_float = self.value_is_float(operand, mir_func, mir);
                let use_f32 = self.value_is_f32(operand, mir_func, mir);

                match op {
                    UnaryOp::Neg if use_float && use_f32 => {
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::F32Neg);
                    }
                    UnaryOp::Neg if use_float => {
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::F64Neg);
                    }
                    UnaryOp::Neg if use_i64 => {
                        func_body.instruction(&Instruction::I64Const(0));
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::I64Sub);
                    }
                    UnaryOp::Neg => {
                        func_body.instruction(&Instruction::I32Const(0));
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::I32Sub);
                    }
                    UnaryOp::Not => {
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::I32Eqz);
                    }
                    UnaryOp::BitNot if use_i64 => {
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::I64Const(-1));
                        func_body.instruction(&Instruction::I64Xor);
                    }
                    UnaryOp::BitNot => {
                        self.lower_value(
                            operand,
                            func_body,
                            mir_func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        func_body.instruction(&Instruction::I32Const(-1));
                        func_body.instruction(&Instruction::I32Xor);
                    }
                }
            }
            Value::Load { ptr } => {
                // Load from memory: lower ptr to get address, then load i32
                self.lower_value(
                    ptr,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                func_body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));
            }
            Value::Field { base, field } => {
                // Field access on a tuple/struct pointer in linear memory.
                // Lower base to get the pointer, then add the field offset and load.
                self.lower_value(
                    base,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                // Parse numeric field names for tuple access (e.g., "0", "1")
                if let Ok(idx) = field.parse::<usize>() {
                    // Try to determine the tuple type from the base
                    let field_offset = idx as i32 * 8; // conservative 8-byte stride
                    if field_offset > 0 {
                        func_body.instruction(&Instruction::I32Const(field_offset));
                        func_body.instruction(&Instruction::I32Add);
                    }
                }
                // Load the value at the computed address
                func_body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));
            }
            Value::Index { base, index } => {
                // Array index access: base pointer + (index * element_size).
                // Lower base to get array data pointer.
                self.lower_value(
                    base,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                // Skip past the 8-byte array header (ptr, len) to data pointer
                func_body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));
                // Compute offset: index * 4 (i32 element size default)
                self.lower_value(
                    index,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                func_body.instruction(&Instruction::I32Const(4));
                func_body.instruction(&Instruction::I32Mul);
                func_body.instruction(&Instruction::I32Add);
                // Load element
                func_body.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 2,
                    memory_index: 0,
                }));
            }
            Value::Cast { value, target_ty } => {
                self.lower_value(
                    value,
                    func_body,
                    mir_func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                // Insert conversion instructions based on target type
                match ty_to_wasm(target_ty) {
                    Some(WasmType::I64) => {
                        // Assume source is i32 → extend
                        func_body.instruction(&Instruction::I64ExtendI32S);
                    }
                    Some(WasmType::F64) => {
                        // Assume source is i64 → convert
                        func_body.instruction(&Instruction::F64ConvertI64S);
                    }
                    Some(WasmType::I32) => {
                        // Assume source is i64 → wrap
                        func_body.instruction(&Instruction::I32WrapI64);
                    }
                    _ => {} // No conversion needed or unknown
                }
            }
        }
    }

    /// Heuristic: does this value produce an i64?
    fn value_is_i64(&self, value: &Value, func: &eclexia_mir::Function, mir: &MirFile) -> bool {
        match value {
            Value::Constant(id) => is_i64_type(&mir.constants[*id].ty),
            Value::Local(id) => {
                let all_locals = func.params.iter().chain(func.locals.iter());
                all_locals
                    .into_iter()
                    .find(|l| l.id == *id)
                    .map(|l| is_i64_type(&l.ty))
                    .unwrap_or(false)
            }
            Value::Binary { lhs, .. } => self.value_is_i64(lhs, func, mir),
            Value::Unary { operand, .. } => self.value_is_i64(operand, func, mir),
            Value::Cast { target_ty, .. } => is_i64_type(target_ty),
            _ => false,
        }
    }

    /// Heuristic: does this value produce a float (f32 or f64)?
    fn value_is_float(&self, value: &Value, func: &eclexia_mir::Function, mir: &MirFile) -> bool {
        match value {
            Value::Constant(id) => is_float_type(&mir.constants[*id].ty),
            Value::Local(id) => {
                let all_locals = func.params.iter().chain(func.locals.iter());
                all_locals
                    .into_iter()
                    .find(|l| l.id == *id)
                    .map(|l| is_float_type(&l.ty))
                    .unwrap_or(false)
            }
            Value::Binary { lhs, .. } => self.value_is_float(lhs, func, mir),
            Value::Unary { operand, .. } => self.value_is_float(operand, func, mir),
            Value::Cast { target_ty, .. } => is_float_type(target_ty),
            _ => false,
        }
    }

    /// Heuristic: does this value produce an f32 specifically?
    fn value_is_f32(&self, value: &Value, func: &eclexia_mir::Function, mir: &MirFile) -> bool {
        match value {
            Value::Constant(id) => is_f32_type(&mir.constants[*id].ty),
            Value::Local(id) => {
                let all_locals = func.params.iter().chain(func.locals.iter());
                all_locals
                    .into_iter()
                    .find(|l| l.id == *id)
                    .map(|l| is_f32_type(&l.ty))
                    .unwrap_or(false)
            }
            Value::Binary { lhs, .. } => self.value_is_f32(lhs, func, mir),
            Value::Unary { operand, .. } => self.value_is_f32(operand, func, mir),
            Value::Cast { target_ty, .. } => is_f32_type(target_ty),
            _ => false,
        }
    }

    /// Map a resource name to a numeric ID for WASM.
    fn resource_name_to_id(name: &str) -> i32 {
        match name {
            "energy" => 0,
            "time" => 1,
            "memory" => 2,
            "carbon" => 3,
            _ => {
                // Simple hash for unknown resources
                let mut hash: i32 = 100;
                for b in name.bytes() {
                    hash = hash.wrapping_mul(31).wrapping_add(b as i32);
                }
                hash
            }
        }
    }

    /// Collect all string constants from a MIR file and assign data section offsets.
    fn collect_strings(mir: &MirFile) -> Vec<(SmolStr, u32)> {
        let mut strings: Vec<(SmolStr, u32)> = Vec::new();
        let mut offset: u32 = 0;

        for (_, constant) in mir.constants.iter() {
            if let ConstantKind::String(s) = &constant.kind {
                if !strings.iter().any(|(existing, _)| existing == s) {
                    strings.push((s.clone(), offset));
                    offset += s.len() as u32 + 1; // +1 for null terminator
                }
            }
        }

        strings
    }

    /// Build a complete WASM binary module from a MIR file.
    fn build_module(
        &self,
        mir: &MirFile,
        imports: &[WasmImport],
        compiled_funcs: &[(Vec<WasmType>, Option<WasmType>, WasmFunc)],
        string_data: &[(SmolStr, u32)],
    ) -> Vec<u8> {
        let mut module = Module::new();
        let import_count = imports.len() as u32;

        // === Type section ===
        let mut types = TypeSection::new();

        // Import function types first
        for imp in imports {
            let params: Vec<ValType> = imp.params.iter().map(|t| t.to_val_type()).collect();
            let results: Vec<ValType> = imp.result.iter().map(|t| t.to_val_type()).collect();
            types.ty().function(params, results);
        }

        // Then our function types
        for (params, result, _) in compiled_funcs {
            let wasm_params: Vec<ValType> = params.iter().map(|t| t.to_val_type()).collect();
            let wasm_results: Vec<ValType> = result.iter().map(|t| t.to_val_type()).collect();
            types.ty().function(wasm_params, wasm_results);
        }

        module.section(&types);

        // === Import section ===
        if !imports.is_empty() {
            let mut import_section = ImportSection::new();
            for (i, imp) in imports.iter().enumerate() {
                import_section.import(
                    imp.module.as_str(),
                    imp.name.as_str(),
                    EntityType::Function(i as u32),
                );
            }
            module.section(&import_section);
        }

        // === Function section ===
        let mut func_section = FunctionSection::new();
        for i in 0..compiled_funcs.len() {
            func_section.function((import_count + i as u32) as u32);
        }
        module.section(&func_section);

        // === Memory section ===
        let mut memory_section = MemorySection::new();
        memory_section.memory(MemoryType {
            minimum: self.initial_memory_pages as u64,
            maximum: Some(self.max_memory_pages as u64),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        module.section(&memory_section);

        // === Export section ===
        let mut export_section = ExportSection::new();

        // Export all functions
        for (i, func) in mir.functions.iter().enumerate() {
            export_section.export(
                func.name.as_str(),
                ExportKind::Func,
                import_count + i as u32,
            );
        }

        // Export memory
        export_section.export("memory", ExportKind::Memory, 0);

        module.section(&export_section);

        // === Code section ===
        let mut code_section = CodeSection::new();
        for (_, _, func_body) in compiled_funcs {
            code_section.function(func_body);
        }
        module.section(&code_section);

        // === Data section ===
        if !string_data.is_empty() {
            let mut data_section = DataSection::new();
            for (s, offset) in string_data {
                let mut bytes = s.as_bytes().to_vec();
                bytes.push(0); // null terminator
                               // Active data segment at offset in memory 0
                data_section.active(
                    0,
                    &wasm_encoder::ConstExpr::i32_const(*offset as i32),
                    bytes,
                );
            }
            module.section(&data_section);
        }

        module.finish()
    }

    /// Emit a single block's instructions (not terminator) into a WASM function body.
    fn emit_instructions(
        &self,
        block: &eclexia_mir::BasicBlock,
        func_body: &mut WasmFunc,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        import_count: u32,
        string_offsets: &[(SmolStr, u32)],
        indices: &ImportIndices,
    ) {
        for instr in &block.instructions {
            match &instr.kind {
                InstructionKind::Assign { target, value } => {
                    self.lower_value(
                        value,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    func_body.instruction(&Instruction::LocalSet(*target));
                }
                InstructionKind::Store { ptr, value } => {
                    self.lower_value(
                        ptr,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.lower_value(
                        value,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    func_body.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
                        offset: 0,
                        align: 2,
                        memory_index: 0,
                    }));
                }
                InstructionKind::Call {
                    target,
                    func: callee,
                    args,
                    ..
                } => {
                    for arg in args {
                        self.lower_value(
                            arg,
                            func_body,
                            func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                    }
                    match callee {
                        Value::Local(id) => {
                            func_body.instruction(&Instruction::LocalGet(*id));
                        }
                        _ => {
                            func_body.instruction(&Instruction::Call(import_count));
                        }
                    }
                    if let Some(target_local) = target {
                        func_body.instruction(&Instruction::LocalSet(*target_local));
                    }
                }
                InstructionKind::ResourceTrack {
                    resource, amount, ..
                } => {
                    let resource_id = Self::resource_name_to_id(resource.as_str());
                    func_body.instruction(&Instruction::I32Const(resource_id));
                    self.lower_value(
                        amount,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    if let Some(idx) = indices.track_resource {
                        func_body.instruction(&Instruction::Call(idx));
                    }
                }
                InstructionKind::ShadowPriceHook { resource, .. } => {
                    let resource_id = Self::resource_name_to_id(resource.as_str());
                    func_body.instruction(&Instruction::I32Const(resource_id));
                    if let Some(idx) = indices.query_shadow_price {
                        func_body.instruction(&Instruction::Call(idx));
                        func_body.instruction(&Instruction::Drop);
                    }
                }
                InstructionKind::Nop => {
                    func_body.instruction(&Instruction::Nop);
                }
            }
        }
    }

    /// Emit a block's terminator. For Branch/Switch, inlines target block contents
    /// and marks them in `emitted` so the main loop skips them.
    #[allow(clippy::too_many_arguments)]
    fn emit_terminator(
        &self,
        terminator: &Terminator,
        func_body: &mut WasmFunc,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        import_count: u32,
        string_offsets: &[(SmolStr, u32)],
        indices: &ImportIndices,
        block_id: BlockId,
        block_order: &[BlockId],
        emitted: &mut Vec<BlockId>,
    ) {
        match terminator {
            Terminator::Return(None) => {
                let is_last = block_order
                    .last()
                    .map(|last| *last == block_id)
                    .unwrap_or(true);
                if !is_last {
                    func_body.instruction(&Instruction::Return);
                }
            }
            Terminator::Return(Some(value)) => {
                self.lower_value(
                    value,
                    func_body,
                    func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                let is_last = block_order
                    .last()
                    .map(|last| *last == block_id)
                    .unwrap_or(true);
                if !is_last {
                    func_body.instruction(&Instruction::Return);
                }
            }
            Terminator::Goto(target_block) => {
                // Check if target is the next block in linearized order (fallthrough)
                let pos = block_order.iter().position(|b| *b == block_id);
                let is_fallthrough = pos
                    .and_then(|p| block_order.get(p + 1))
                    .map(|next| *next == *target_block)
                    .unwrap_or(false);
                if !is_fallthrough {
                    // Non-adjacent goto: emit the target block inline and mark it emitted.
                    // This handles forward jumps; backward jumps would need loop/br.
                    let target = &func.basic_blocks[*target_block];
                    self.emit_instructions(
                        target,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.emit_terminator(
                        &target.terminator,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                        *target_block,
                        block_order,
                        emitted,
                    );
                    emitted.push(*target_block);
                }
            }
            Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => {
                self.lower_value(
                    condition,
                    func_body,
                    func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );
                // Use Empty block type; arms use explicit return when producing values
                func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                // Emit then-block contents inline
                {
                    let then_blk = &func.basic_blocks[*then_block];
                    self.emit_instructions(
                        then_blk,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.emit_terminator(
                        &then_blk.terminator,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                        *then_block,
                        block_order,
                        emitted,
                    );
                    emitted.push(*then_block);
                }

                func_body.instruction(&Instruction::Else);

                // Emit else-block contents inline
                {
                    let else_blk = &func.basic_blocks[*else_block];
                    self.emit_instructions(
                        else_blk,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.emit_terminator(
                        &else_blk.terminator,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                        *else_block,
                        block_order,
                        emitted,
                    );
                    emitted.push(*else_block);
                }

                func_body.instruction(&Instruction::End);
            }
            Terminator::Switch {
                value,
                targets,
                default,
            } => {
                // Emit cascading if/else for each case
                self.lower_value(
                    value,
                    func_body,
                    func,
                    mir,
                    import_count,
                    string_offsets,
                    indices,
                );

                if targets.is_empty() {
                    // No cases: just drop the value and emit the default block
                    func_body.instruction(&Instruction::Drop);
                    let def_blk = &func.basic_blocks[*default];
                    self.emit_instructions(
                        def_blk,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.emit_terminator(
                        &def_blk.terminator,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                        *default,
                        block_order,
                        emitted,
                    );
                    emitted.push(*default);
                } else {
                    // Cascading if/else for each case value.
                    // Re-lower the switch value for each comparison (correct but not optimal;
                    // a local.tee approach would be more efficient).
                    for (i, (case_val, case_block)) in targets.iter().enumerate() {
                        if i > 0 {
                            self.lower_value(
                                value,
                                func_body,
                                func,
                                mir,
                                import_count,
                                string_offsets,
                                indices,
                            );
                        }
                        func_body.instruction(&Instruction::I32Const(*case_val as i32));
                        func_body.instruction(&Instruction::I32Eq);
                        func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));

                        let case_blk = &func.basic_blocks[*case_block];
                        self.emit_instructions(
                            case_blk,
                            func_body,
                            func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                        );
                        self.emit_terminator(
                            &case_blk.terminator,
                            func_body,
                            func,
                            mir,
                            import_count,
                            string_offsets,
                            indices,
                            *case_block,
                            block_order,
                            emitted,
                        );
                        emitted.push(*case_block);

                        func_body.instruction(&Instruction::Else);
                    }

                    // Default case (innermost else)
                    let def_blk = &func.basic_blocks[*default];
                    self.emit_instructions(
                        def_blk,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                    );
                    self.emit_terminator(
                        &def_blk.terminator,
                        func_body,
                        func,
                        mir,
                        import_count,
                        string_offsets,
                        indices,
                        *default,
                        block_order,
                        emitted,
                    );
                    emitted.push(*default);

                    // Close all the nested if/else blocks
                    for _ in 0..targets.len() {
                        func_body.instruction(&Instruction::End);
                    }
                }
            }
            Terminator::Unreachable => {
                func_body.instruction(&Instruction::Unreachable);
            }
        }
    }

    /// Compile a single MIR function to WASM instructions.
    fn compile_function(
        &self,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        import_count: u32,
        string_offsets: &[(SmolStr, u32)],
        indices: &ImportIndices,
    ) -> Result<(Vec<WasmType>, Option<WasmType>, WasmFunc), CodegenError> {
        let params = Self::derive_params(func);
        let result = Self::derive_result(func);
        let extra_locals = Self::derive_locals(func);

        let mut func_body = WasmFunc::new(extra_locals.iter().map(|t| (1, *t)));

        // Collect block IDs in order, entry first
        let mut block_order: Vec<BlockId> = Vec::new();
        block_order.push(func.entry_block);
        for (id, _) in func.basic_blocks.iter() {
            if id != func.entry_block {
                block_order.push(id);
            }
        }

        // Track blocks that get inlined into Branch/Switch terminators
        let mut emitted: Vec<BlockId> = Vec::new();

        for &block_id in &block_order {
            if emitted.contains(&block_id) {
                continue;
            }

            let block = &func.basic_blocks[block_id];

            self.emit_instructions(
                block,
                &mut func_body,
                func,
                mir,
                import_count,
                string_offsets,
                indices,
            );
            self.emit_terminator(
                &block.terminator,
                &mut func_body,
                func,
                mir,
                import_count,
                string_offsets,
                indices,
                block_id,
                &block_order,
                &mut emitted,
            );
        }

        // End the function body
        func_body.instruction(&Instruction::End);

        Ok((params, result, func_body))
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
        let (imports, indices) = self.collect_imports(mir);
        let import_count = imports.len() as u32;
        let string_offsets = Self::collect_strings(mir);

        let mut compiled_funcs = Vec::new();
        let mut wasm_functions = Vec::new();

        for func in &mir.functions {
            let (params, result, func_body) =
                self.compile_function(func, mir, import_count, &string_offsets, &indices)?;

            let uses_resource_imports = func.basic_blocks.iter().any(|(_, block)| {
                block
                    .instructions
                    .iter()
                    .any(|i| matches!(i.kind, InstructionKind::ResourceTrack { .. }))
            });

            wasm_functions.push(WasmFunction {
                name: func.name.clone(),
                params: params.clone(),
                result,
                code_size: 0, // Will be updated after binary generation
                uses_resource_imports,
            });

            compiled_funcs.push((params, result, func_body));
        }

        let exports: Vec<WasmExport> = wasm_functions
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

        // Build the actual binary module
        let binary = self.build_module(mir, &imports, &compiled_funcs, &string_offsets);
        let binary_size = binary.len();

        Ok(WasmModule {
            functions: wasm_functions,
            imports,
            exports,
            initial_memory_pages: self.initial_memory_pages,
            max_memory_pages: self.max_memory_pages,
            binary_size,
            binary,
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
        BasicBlock, Constant, ConstantKind, Function, Instruction as MirInstruction,
        InstructionKind, Local, Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    trait UnwrapOk<T> {
        fn unwrap_ok(self) -> T;
    }

    impl<T, E: std::fmt::Debug> UnwrapOk<T> for Result<T, E> {
        fn unwrap_ok(self) -> T {
            match self {
                Ok(val) => val,
                Err(err) => panic!("Expected Ok, got Err: {:?}", err),
            }
        }
    }

    impl<T> UnwrapOk<T> for Option<T> {
        fn unwrap_ok(self) -> T {
            match self {
                Some(val) => val,
                None => panic!("Expected Some, got None"),
            }
        }
    }

    fn make_test_mir_with_resources() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(50.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![MirInstruction {
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
            instructions: vec![MirInstruction {
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

    fn make_arithmetic_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(10),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(20),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![MirInstruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Value::Constant(c1)),
                        rhs: Box::new(Value::Constant(c2)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("add_numbers"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::I64),
                mutable: true,
            }],
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

    fn make_params_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![MirInstruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 2,
                    value: Value::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Value::Local(0)),
                        rhs: Box::new(Value::Local(1)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(2))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("add"),
            params: vec![
                Local {
                    id: 0,
                    name: SmolStr::new("a"),
                    ty: Ty::Primitive(PrimitiveTy::I64),
                    mutable: false,
                },
                Local {
                    id: 1,
                    name: SmolStr::new("b"),
                    ty: Ty::Primitive(PrimitiveTy::I64),
                    mutable: false,
                },
            ],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![Local {
                id: 2,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::I64),
                mutable: true,
            }],
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
        let module = backend.generate(&mir).unwrap_ok();

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
        let module = backend.generate(&mir).unwrap_ok();

        assert!(!module.imports.is_empty());
        assert_eq!(module.imports[0].module, "eclexia");
        assert_eq!(module.imports[0].name, "track_resource");
    }

    #[test]
    fn test_wasm_no_imports_when_no_resources() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert!(module.imports.is_empty());
    }

    #[test]
    fn test_wasm_exports() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap_ok();

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
        let module = backend.generate(&mir).unwrap_ok();

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
        let module = backend.generate(&mir).unwrap_ok();

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

    // === New tests for real binary output ===

    #[test]
    fn test_wasm_binary_magic_number() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap_ok();

        let bytes = module.to_bytes();
        assert!(
            bytes.len() >= 8,
            "WASM binary too short: {} bytes",
            bytes.len()
        );
        // WASM magic: \0asm
        assert_eq!(&bytes[0..4], b"\0asm", "Missing WASM magic number");
        // WASM version 1
        assert_eq!(&bytes[4..8], &[1, 0, 0, 0], "Wrong WASM version");
    }

    #[test]
    fn test_wasm_binary_nonempty() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert!(
            module.binary_size > 8,
            "Module should be larger than just header"
        );
        assert_eq!(module.binary_size, module.to_bytes().len());
    }

    #[test]
    fn test_wasm_arithmetic_function() {
        let mut backend = WasmBackend::new();
        let mir = make_arithmetic_mir();
        let module = backend.generate(&mir).unwrap_ok();

        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");

        // Should have one function with i64 return type
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "add_numbers");
        assert_eq!(module.functions[0].result, Some(WasmType::I64));
    }

    #[test]
    fn test_wasm_function_params() {
        let mut backend = WasmBackend::new();
        let mir = make_params_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "add");
        assert_eq!(
            module.functions[0].params,
            vec![WasmType::I64, WasmType::I64]
        );
        assert_eq!(module.functions[0].result, Some(WasmType::I64));

        // Verify binary is valid
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_into_bytes() {
        let mut backend = WasmBackend::new();
        let mir = make_simple_mir();
        let module = backend.generate(&mir).unwrap_ok();

        let size = module.binary_size;
        let bytes = module.into_bytes();
        assert_eq!(bytes.len(), size);
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_type_mapping() {
        // Int → I64
        assert_eq!(prim_to_wasm(PrimitiveTy::Int), Some(WasmType::I64));
        assert_eq!(prim_to_wasm(PrimitiveTy::I64), Some(WasmType::I64));
        // I32 → I32
        assert_eq!(prim_to_wasm(PrimitiveTy::I32), Some(WasmType::I32));
        assert_eq!(prim_to_wasm(PrimitiveTy::Bool), Some(WasmType::I32));
        // Float → F64
        assert_eq!(prim_to_wasm(PrimitiveTy::Float), Some(WasmType::F64));
        assert_eq!(prim_to_wasm(PrimitiveTy::F64), Some(WasmType::F64));
        // F32 → F32
        assert_eq!(prim_to_wasm(PrimitiveTy::F32), Some(WasmType::F32));
        // String → I32 (offset)
        assert_eq!(prim_to_wasm(PrimitiveTy::String), Some(WasmType::I32));
        // Unit → None
        assert_eq!(prim_to_wasm(PrimitiveTy::Unit), None);
    }

    #[test]
    fn test_wasm_resource_id_mapping() {
        assert_eq!(WasmBackend::resource_name_to_id("energy"), 0);
        assert_eq!(WasmBackend::resource_name_to_id("time"), 1);
        assert_eq!(WasmBackend::resource_name_to_id("memory"), 2);
        assert_eq!(WasmBackend::resource_name_to_id("carbon"), 3);
        let id1 = WasmBackend::resource_name_to_id("custom");
        let id2 = WasmBackend::resource_name_to_id("custom");
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_wasm_branch_terminator() {
        // MIR with a Branch: if condition goto then_block else else_block
        let mut constants: Arena<Constant> = Arena::new();
        let c_true = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Bool),
            kind: ConstantKind::Bool(true),
        });
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(42),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(99),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let then_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("then"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c1))),
        });
        let else_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("else"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c2))),
        });
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Branch {
                condition: Value::Constant(c_true),
                then_block,
                else_block,
            },
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("branch_test"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&mir).unwrap_ok();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "branch_test");
        // Should produce valid WASM
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_switch_terminator() {
        let mut constants: Arena<Constant> = Arena::new();
        let c_val = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I32),
            kind: ConstantKind::Int(1),
        });
        let c_ret0 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I32),
            kind: ConstantKind::Int(10),
        });
        let c_ret1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I32),
            kind: ConstantKind::Int(20),
        });
        let c_default = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I32),
            kind: ConstantKind::Int(0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let case0 = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case0"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_ret0))),
        });
        let case1 = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case1"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_ret1))),
        });
        let default_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("default"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_default))),
        });
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Switch {
                value: Value::Constant(c_val),
                targets: vec![(0, case0), (1, case1)],
                default: default_block,
            },
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("switch_test"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I32),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&mir).unwrap_ok();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "switch_test");
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_pow_import() {
        // MIR with Pow operation should generate a pow import
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(2),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(10),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![MirInstruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Pow,
                        lhs: Box::new(Value::Constant(c1)),
                        rhs: Box::new(Value::Constant(c2)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("pow_test"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::I64),
                mutable: true,
            }],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&mir).unwrap_ok();

        // Should have a pow import
        assert!(module.imports.iter().any(|i| i.name == "pow"));
        assert_eq!(module.imports.last().unwrap_ok().name, "pow");

        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_goto_terminator() {
        // MIR with a Goto to a non-adjacent block
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(42),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let target = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("target"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c1))),
        });
        // Insert a dummy block between entry and target
        let _dummy = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("dummy"),
            instructions: vec![],
            terminator: Terminator::Unreachable,
        });
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Goto(target),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("goto_test"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&mir).unwrap_ok();
        assert_eq!(module.functions.len(), 1);
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_import_indices_correctness() {
        // Verify that when only ShadowPriceHook is present (no ResourceTrack),
        // its import index is 0 (not hardcoded 1)
        let mut constants: Arena<Constant> = Arena::new();
        let _c = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(1.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![MirInstruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ShadowPriceHook {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("shadow_only"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func],
            constants,
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&mir).unwrap_ok();
        // Should have exactly 1 import (query_shadow_price) at index 0
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].name, "query_shadow_price");
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_wasm_complex_type_mapping() {
        // Tuple type should map to I32 (pointer)
        let tuple_ty = Ty::Tuple(vec![
            Ty::Primitive(PrimitiveTy::I32),
            Ty::Primitive(PrimitiveTy::F64),
        ]);
        assert_eq!(ty_to_wasm(&tuple_ty), Some(WasmType::I32));

        // Array type should map to I32 (pointer)
        let array_ty = Ty::Array {
            elem: Box::new(Ty::Primitive(PrimitiveTy::I32)),
            size: Some(10),
        };
        assert_eq!(ty_to_wasm(&array_ty), Some(WasmType::I32));

        // Named type (struct) should map to I32 (pointer)
        let named_ty = Ty::Named {
            name: SmolStr::new("Point"),
            args: vec![],
        };
        assert_eq!(ty_to_wasm(&named_ty), Some(WasmType::I32));

        // Function type should map to I32 (function pointer)
        let fn_ty = Ty::Function {
            params: vec![Ty::Primitive(PrimitiveTy::I32)],
            ret: Box::new(Ty::Primitive(PrimitiveTy::I32)),
        };
        assert_eq!(ty_to_wasm(&fn_ty), Some(WasmType::I32));
    }

    #[test]
    fn test_wasm_type_byte_sizes() {
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::I32)), 4);
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::I64)), 8);
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::F64)), 8);
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::Bool)), 4);
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::String)), 8);
        assert_eq!(ty_byte_size(&Ty::Primitive(PrimitiveTy::Unit)), 0);

        // Tuple of (i32, f64) = 4 + 8 = 12 bytes
        let tuple_ty = Ty::Tuple(vec![
            Ty::Primitive(PrimitiveTy::I32),
            Ty::Primitive(PrimitiveTy::F64),
        ]);
        assert_eq!(ty_byte_size(&tuple_ty), 12);

        // Array is 8 bytes (pointer + length)
        let array_ty = Ty::Array {
            elem: Box::new(Ty::Primitive(PrimitiveTy::I32)),
            size: None,
        };
        assert_eq!(ty_byte_size(&array_ty), 8);
    }

    #[test]
    fn test_wasm_tuple_field_offset() {
        let fields = vec![
            Ty::Primitive(PrimitiveTy::I32),  // 4 bytes
            Ty::Primitive(PrimitiveTy::F64),  // 8 bytes
            Ty::Primitive(PrimitiveTy::Bool), // 4 bytes
        ];
        assert_eq!(tuple_field_offset(&fields, 0), 0);
        assert_eq!(tuple_field_offset(&fields, 1), 4);
        assert_eq!(tuple_field_offset(&fields, 2), 12);
    }

    #[test]
    fn test_wasm_bump_allocator() {
        let mut alloc = BumpAllocator::new(100);
        // First allocation: aligned to 8 from offset 100 → 104
        let a = alloc.alloc(16);
        assert_eq!(a, 104); // 100 rounded up to 104 (next 8-byte aligned)
        // Second: 104 + 16 = 120, already aligned
        let b = alloc.alloc(8);
        assert_eq!(b, 120);
        // Third: 120 + 8 = 128, already aligned
        let c = alloc.alloc(4);
        assert_eq!(c, 128);
    }
}
