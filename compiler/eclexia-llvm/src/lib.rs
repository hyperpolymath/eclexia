// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! LLVM native code backend for Eclexia.
//!
//! Generates textual LLVM IR (`.ll` files) from Eclexia MIR. The output can
//! be compiled to native code with `llc` or consumed by any LLVM-based toolchain.
//!
//! ## Design
//!
//! - **Textual IR**: No LLVM library dependency — emits human-readable `.ll` files.
//! - **Alloca-based locals**: All locals use `alloca` + `load`/`store`. LLVM's
//!   `mem2reg` pass promotes these to SSA at `-O1` and above.
//! - **Opaque pointers**: Uses `ptr` (LLVM 15+) rather than typed pointers.
//! - **Zero new dependencies**: Pure string generation using existing crate deps.
//!
//! ## Usage
//!
//! ```ignore
//! let mut backend = LlvmBackend::new();
//! let module = backend.generate(&mir)?;
//! module.write_to_file("output.ll")?;
//! // Optionally compile: llc -O2 output.ll -o output.o
//! ```

use eclexia_ast::types::{PrimitiveTy, Ty};
use eclexia_codegen::{Backend, CodegenError};
use eclexia_mir::{
    BasicBlock, BinaryOp, BlockId, ConstantKind, Function, InstructionKind, MirFile, Terminator,
    UnaryOp, Value,
};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

// ---------------------------------------------------------------------------
// Type mapping
// ---------------------------------------------------------------------------

/// Map an Eclexia `Ty` to its LLVM IR type string.
fn ty_to_llvm(ty: &Ty) -> &'static str {
    match ty {
        Ty::Primitive(p) => prim_to_llvm(*p),
        Ty::Resource { base, .. } => prim_to_llvm(*base),
        Ty::Named { .. }
        | Ty::Function { .. }
        | Ty::Tuple(_)
        | Ty::Array { .. }
        | Ty::ForAll { .. }
        | Ty::Var(_)
        | Ty::Error
        | Ty::Never => "ptr",
    }
}

/// Map an Eclexia `PrimitiveTy` to its LLVM IR type string.
fn prim_to_llvm(p: PrimitiveTy) -> &'static str {
    match p {
        PrimitiveTy::Bool => "i1",
        PrimitiveTy::I8 | PrimitiveTy::U8 => "i8",
        PrimitiveTy::I16 | PrimitiveTy::U16 => "i16",
        PrimitiveTy::I32 | PrimitiveTy::U32 | PrimitiveTy::Char => "i32",
        PrimitiveTy::Int
        | PrimitiveTy::I64
        | PrimitiveTy::U64
        | PrimitiveTy::UInt
        | PrimitiveTy::I128
        | PrimitiveTy::U128 => "i64",
        PrimitiveTy::F32 => "float",
        PrimitiveTy::Float | PrimitiveTy::F64 => "double",
        PrimitiveTy::String => "ptr",
        PrimitiveTy::Unit => "void",
    }
}

/// Check if a primitive type is a float type.
fn is_float_prim(p: PrimitiveTy) -> bool {
    p.is_float()
}

/// Format a 64-bit float as LLVM hex representation.
/// LLVM expects `0xHHHHHHHHHHHHHHHH` (IEEE 754 double).
fn format_float_hex(f: f64) -> String {
    let bits = f.to_bits();
    format!("0x{:016X}", bits)
}

/// Determine the LLVM type for a Value by tracing through to constants/locals.
fn infer_value_llvm_type<'a>(value: &Value, func: &Function, mir: &MirFile) -> &'static str {
    match value {
        Value::Constant(id) => ty_to_llvm(&mir.constants[*id].ty),
        Value::Local(id) => {
            let all_locals = func.params.iter().chain(func.locals.iter());
            all_locals
                .into_iter()
                .find(|l| l.id == *id)
                .map(|l| ty_to_llvm(&l.ty))
                .unwrap_or("i64")
        }
        Value::Binary { op, lhs, .. } => {
            // Comparison ops always return i1
            match op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge => "i1",
                BinaryOp::And | BinaryOp::Or => "i1",
                _ => infer_value_llvm_type(lhs, func, mir),
            }
        }
        Value::Unary { op, operand } => match op {
            UnaryOp::Not => "i1",
            _ => infer_value_llvm_type(operand, func, mir),
        },
        Value::Cast { target_ty, .. } => ty_to_llvm(target_ty),
        Value::Load { .. } | Value::Field { .. } | Value::Index { .. } => "i64",
    }
}

/// Check if a Value produces a float type.
fn value_is_float(value: &Value, func: &Function, mir: &MirFile) -> bool {
    match value {
        Value::Constant(id) => match &mir.constants[*id].ty {
            Ty::Primitive(p) => is_float_prim(*p),
            Ty::Resource { base, .. } => is_float_prim(*base),
            _ => false,
        },
        Value::Local(id) => {
            let all_locals = func.params.iter().chain(func.locals.iter());
            all_locals
                .into_iter()
                .find(|l| l.id == *id)
                .map(|l| match &l.ty {
                    Ty::Primitive(p) => is_float_prim(*p),
                    Ty::Resource { base, .. } => is_float_prim(*base),
                    _ => false,
                })
                .unwrap_or(false)
        }
        Value::Binary { lhs, .. } => value_is_float(lhs, func, mir),
        Value::Unary { operand, .. } => value_is_float(operand, func, mir),
        Value::Cast { target_ty, .. } => match target_ty {
            Ty::Primitive(p) => is_float_prim(*p),
            _ => false,
        },
        _ => false,
    }
}

/// Check if a Value produces an f32 specifically.
fn value_is_f32(value: &Value, func: &Function, mir: &MirFile) -> bool {
    match value {
        Value::Constant(id) => matches!(&mir.constants[*id].ty, Ty::Primitive(PrimitiveTy::F32)),
        Value::Local(id) => {
            let all_locals = func.params.iter().chain(func.locals.iter());
            all_locals
                .into_iter()
                .find(|l| l.id == *id)
                .map(|l| matches!(&l.ty, Ty::Primitive(PrimitiveTy::F32)))
                .unwrap_or(false)
        }
        Value::Binary { lhs, .. } => value_is_f32(lhs, func, mir),
        Value::Unary { operand, .. } => value_is_f32(operand, func, mir),
        Value::Cast { target_ty, .. } => matches!(target_ty, Ty::Primitive(PrimitiveTy::F32)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Module context — tracks string constants and extern declarations
// ---------------------------------------------------------------------------

struct ModuleContext {
    /// Interned string constants: (content, global name like `@.str.0`).
    string_constants: Vec<(String, String)>,
    /// External function declarations (e.g. `declare void @__eclexia_track_resource(...)`).
    extern_decls: Vec<String>,
    /// Function name → LLVM function index (for call resolution).
    function_indices: FxHashMap<SmolStr, usize>,
    next_str_id: usize,
}

impl ModuleContext {
    fn new() -> Self {
        Self {
            string_constants: Vec::new(),
            extern_decls: Vec::new(),
            function_indices: FxHashMap::default(),
            next_str_id: 0,
        }
    }

    /// Intern a string constant, returning its global name (e.g. `@.str.0`).
    fn intern_string(&mut self, s: &str) -> String {
        // Check if already interned
        for (content, name) in &self.string_constants {
            if content == s {
                return name.clone();
            }
        }
        let name = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        self.string_constants.push((s.to_string(), name.clone()));
        name
    }

    /// Add an external declaration (deduplicating).
    fn declare_extern(&mut self, decl: &str) {
        if !self.extern_decls.iter().any(|d| d == decl) {
            self.extern_decls.push(decl.to_string());
        }
    }

    /// Register a function by name with its index.
    fn register_function(&mut self, name: SmolStr, index: usize) {
        self.function_indices.insert(name, index);
    }

    /// Emit the module header.
    fn emit_header(&self) -> String {
        let mut out = String::new();
        out.push_str("; ModuleID = 'eclexia_module'\n");
        out.push_str("source_filename = \"<input>\"\n");
        out.push_str("target datalayout = \"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128\"\n");
        out.push_str("target triple = \"x86_64-unknown-linux-gnu\"\n");
        out
    }

    /// Emit string constant globals.
    fn emit_string_constants(&self) -> String {
        if self.string_constants.is_empty() {
            return String::new();
        }
        let mut out = String::from("\n; String constants\n");
        for (content, name) in &self.string_constants {
            let escaped = escape_llvm_string(content);
            let len = content.len() + 1; // +1 for null terminator
            out.push_str(&format!(
                "{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"\n",
                name, len, escaped
            ));
        }
        out
    }

    /// Emit external declarations.
    fn emit_extern_decls(&self) -> String {
        if self.extern_decls.is_empty() {
            return String::new();
        }
        let mut out = String::from("\n; Runtime declarations\n");
        for decl in &self.extern_decls {
            out.push_str(decl);
            out.push('\n');
        }
        out
    }
}

/// Escape a string for LLVM IR constant syntax.
fn escape_llvm_string(s: &str) -> String {
    let mut out = String::new();
    for b in s.bytes() {
        if b == b'\\' {
            out.push_str("\\5C");
        } else if b == b'"' {
            out.push_str("\\22");
        } else if b == b'\n' {
            out.push_str("\\0A");
        } else if b == b'\r' {
            out.push_str("\\0D");
        } else if b == b'\t' {
            out.push_str("\\09");
        } else if b == 0 {
            out.push_str("\\00");
        } else if b >= 0x20 && b < 0x7F {
            out.push(b as char);
        } else {
            out.push_str(&format!("\\{:02X}", b));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// IR builder — tracks SSA register numbering and local alloca slots
// ---------------------------------------------------------------------------

struct IrBuilder {
    next_reg: u32,
    body: String,
    /// LocalId → alloca name (e.g. `%local.0`).
    local_alloca: FxHashMap<u32, String>,
}

impl IrBuilder {
    fn new() -> Self {
        Self {
            next_reg: 0,
            body: String::new(),
            local_alloca: FxHashMap::default(),
        }
    }

    /// Allocate a fresh SSA register name.
    fn fresh_reg(&mut self) -> String {
        let reg = format!("%{}", self.next_reg);
        self.next_reg += 1;
        reg
    }

    /// Emit an instruction line (with leading whitespace).
    fn emit(&mut self, line: &str) {
        self.body.push_str("  ");
        self.body.push_str(line);
        self.body.push('\n');
    }

    /// Emit a label.
    fn emit_label(&mut self, label: &str) {
        self.body.push_str(label);
        self.body.push_str(":\n");
    }
}

// ---------------------------------------------------------------------------
// Value lowering
// ---------------------------------------------------------------------------

/// Lower a MIR `Value` to LLVM IR, returning the SSA register (or inline constant)
/// holding the result.
fn lower_value(
    builder: &mut IrBuilder,
    value: &Value,
    func: &Function,
    mir: &MirFile,
    ctx: &mut ModuleContext,
) -> Result<String, CodegenError> {
    match value {
        Value::Local(id) => {
            let alloca_name = builder
                .local_alloca
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("%local.{}", id));
            let ty = local_ty(*id, func);
            if ty == "void" {
                // Unit locals have no loadable value
                return Ok("0".to_string());
            }
            let reg = builder.fresh_reg();
            builder.emit(&format!("{} = load {}, ptr {}", reg, ty, alloca_name));
            Ok(reg)
        }

        Value::Constant(id) => {
            let constant = &mir.constants[*id];
            match &constant.kind {
                ConstantKind::Int(n) => Ok(format!("{}", n)),
                ConstantKind::Float(f) => Ok(format_float_hex(*f)),
                ConstantKind::Bool(b) => Ok(if *b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }),
                ConstantKind::Char(c) => Ok(format!("{}", *c as u32)),
                ConstantKind::Unit => Ok("0".to_string()),
                ConstantKind::String(s) => {
                    let global_name = ctx.intern_string(s.as_str());
                    let len = s.len() + 1;
                    let reg = builder.fresh_reg();
                    builder.emit(&format!(
                        "{} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                        reg, len, global_name
                    ));
                    Ok(reg)
                }
                ConstantKind::Resource { value, .. } => Ok(format_float_hex(*value)),
                ConstantKind::Function(name) => Ok(format!("@{}", name)),
            }
        }

        Value::Binary { op, lhs, rhs } => {
            let lhs_val = lower_value(builder, lhs, func, mir, ctx)?;
            let rhs_val = lower_value(builder, rhs, func, mir, ctx)?;
            let is_float = value_is_float(lhs, func, mir);
            let is_f32 = value_is_f32(lhs, func, mir);
            let operand_ty = infer_value_llvm_type(lhs, func, mir);

            // Float type string for this operation
            let fty = if is_f32 { "float" } else { "double" };
            // Integer type string
            let ity = operand_ty;

            let reg = builder.fresh_reg();

            match op {
                BinaryOp::Add => {
                    if is_float {
                        builder.emit(&format!("{} = fadd {} {}, {}", reg, fty, lhs_val, rhs_val));
                    } else {
                        builder.emit(&format!("{} = add {} {}, {}", reg, ity, lhs_val, rhs_val));
                    }
                }
                BinaryOp::Sub => {
                    if is_float {
                        builder.emit(&format!("{} = fsub {} {}, {}", reg, fty, lhs_val, rhs_val));
                    } else {
                        builder.emit(&format!("{} = sub {} {}, {}", reg, ity, lhs_val, rhs_val));
                    }
                }
                BinaryOp::Mul => {
                    if is_float {
                        builder.emit(&format!("{} = fmul {} {}, {}", reg, fty, lhs_val, rhs_val));
                    } else {
                        builder.emit(&format!("{} = mul {} {}, {}", reg, ity, lhs_val, rhs_val));
                    }
                }
                BinaryOp::Div => {
                    if is_float {
                        builder.emit(&format!("{} = fdiv {} {}, {}", reg, fty, lhs_val, rhs_val));
                    } else {
                        builder.emit(&format!("{} = sdiv {} {}, {}", reg, ity, lhs_val, rhs_val));
                    }
                }
                BinaryOp::Rem => {
                    if is_float {
                        builder.emit(&format!("{} = frem {} {}, {}", reg, fty, lhs_val, rhs_val));
                    } else {
                        builder.emit(&format!("{} = srem {} {}, {}", reg, ity, lhs_val, rhs_val));
                    }
                }
                BinaryOp::Pow => {
                    ctx.declare_extern("declare double @llvm.pow.f64(double, double)");
                    // Always use double for pow
                    builder.emit(&format!(
                        "{} = call double @llvm.pow.f64(double {}, double {})",
                        reg, lhs_val, rhs_val
                    ));
                }
                BinaryOp::Eq => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp oeq {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp eq {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::Ne => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp one {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp ne {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::Lt => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp olt {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp slt {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::Le => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp ole {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp sle {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::Gt => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp ogt {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp sgt {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::Ge => {
                    if is_float {
                        builder.emit(&format!(
                            "{} = fcmp oge {} {}, {}",
                            reg, fty, lhs_val, rhs_val
                        ));
                    } else {
                        builder.emit(&format!(
                            "{} = icmp sge {} {}, {}",
                            reg, ity, lhs_val, rhs_val
                        ));
                    }
                }
                BinaryOp::And => {
                    builder.emit(&format!("{} = and i1 {}, {}", reg, lhs_val, rhs_val));
                }
                BinaryOp::Or => {
                    builder.emit(&format!("{} = or i1 {}, {}", reg, lhs_val, rhs_val));
                }
                BinaryOp::BitAnd => {
                    builder.emit(&format!("{} = and {} {}, {}", reg, ity, lhs_val, rhs_val));
                }
                BinaryOp::BitOr => {
                    builder.emit(&format!("{} = or {} {}, {}", reg, ity, lhs_val, rhs_val));
                }
                BinaryOp::BitXor => {
                    builder.emit(&format!("{} = xor {} {}, {}", reg, ity, lhs_val, rhs_val));
                }
                BinaryOp::Shl => {
                    builder.emit(&format!("{} = shl {} {}, {}", reg, ity, lhs_val, rhs_val));
                }
                BinaryOp::Shr => {
                    builder.emit(&format!("{} = ashr {} {}, {}", reg, ity, lhs_val, rhs_val));
                }
                BinaryOp::Range | BinaryOp::RangeInclusive => {
                    // Range operations need runtime support — emit a call to runtime helper
                    ctx.declare_extern("declare ptr @__eclexia_range(i64, i64, i1)");
                    let inclusive = matches!(op, BinaryOp::RangeInclusive);
                    builder.emit(&format!(
                        "{} = call ptr @__eclexia_range(i64 {}, i64 {}, i1 {})",
                        reg, lhs_val, rhs_val, inclusive
                    ));
                }
            }

            Ok(reg)
        }

        Value::Unary { op, operand } => {
            let operand_val = lower_value(builder, operand, func, mir, ctx)?;
            let is_float = value_is_float(operand, func, mir);
            let is_f32 = value_is_f32(operand, func, mir);
            let operand_ty = infer_value_llvm_type(operand, func, mir);
            let fty = if is_f32 { "float" } else { "double" };

            let reg = builder.fresh_reg();
            match op {
                UnaryOp::Neg => {
                    if is_float {
                        builder.emit(&format!("{} = fneg {} {}", reg, fty, operand_val));
                    } else {
                        builder.emit(&format!("{} = sub {} 0, {}", reg, operand_ty, operand_val));
                    }
                }
                UnaryOp::Not => {
                    builder.emit(&format!("{} = xor i1 {}, true", reg, operand_val));
                }
                UnaryOp::BitNot => {
                    builder.emit(&format!("{} = xor {} {}, -1", reg, operand_ty, operand_val));
                }
            }
            Ok(reg)
        }

        Value::Load { ptr } => {
            let ptr_val = lower_value(builder, ptr, func, mir, ctx)?;
            let reg = builder.fresh_reg();
            builder.emit(&format!("{} = load i64, ptr {}", reg, ptr_val));
            Ok(reg)
        }

        Value::Field { base, .. } | Value::Index { base, .. } => {
            // Not fully supported — lower the base expression
            lower_value(builder, base, func, mir, ctx)
        }

        Value::Cast { value, target_ty } => {
            let src_val = lower_value(builder, value, func, mir, ctx)?;
            let src_ty = infer_value_llvm_type(value, func, mir);
            let dst_ty = ty_to_llvm(target_ty);

            if src_ty == dst_ty {
                return Ok(src_val);
            }

            let reg = builder.fresh_reg();
            let src_is_float = value_is_float(value, func, mir);
            let dst_is_float = matches!(dst_ty, "float" | "double");

            if src_is_float && dst_is_float {
                // Float-to-float conversion
                if dst_ty == "double" {
                    builder.emit(&format!("{} = fpext float {}, double", reg, src_val));
                } else {
                    builder.emit(&format!("{} = fptrunc double {}, float", reg, src_val));
                }
            } else if src_is_float && !dst_is_float {
                // Float-to-int
                builder.emit(&format!(
                    "{} = fptosi {} {}, {}",
                    reg, src_ty, src_val, dst_ty
                ));
            } else if !src_is_float && dst_is_float {
                // Int-to-float
                builder.emit(&format!(
                    "{} = sitofp {} {}, {}",
                    reg, src_ty, src_val, dst_ty
                ));
            } else {
                // Int-to-int — pick sext, trunc, or bitcast based on size
                let src_bits = int_bits(src_ty);
                let dst_bits = int_bits(dst_ty);
                if src_bits < dst_bits {
                    builder.emit(&format!(
                        "{} = sext {} {}, {}",
                        reg, src_ty, src_val, dst_ty
                    ));
                } else if src_bits > dst_bits {
                    builder.emit(&format!(
                        "{} = trunc {} {}, {}",
                        reg, src_ty, src_val, dst_ty
                    ));
                } else {
                    builder.emit(&format!(
                        "{} = bitcast {} {} to {}",
                        reg, src_ty, src_val, dst_ty
                    ));
                }
            }
            Ok(reg)
        }
    }
}

/// Get the bit width of an integer type string.
fn int_bits(ty: &str) -> u32 {
    match ty {
        "i1" => 1,
        "i8" => 8,
        "i16" => 16,
        "i32" => 32,
        "i64" => 64,
        "i128" => 128,
        "ptr" => 64,
        _ => 64,
    }
}

/// Look up the LLVM type for a local variable by ID.
fn local_ty(id: u32, func: &Function) -> &'static str {
    let all_locals = func.params.iter().chain(func.locals.iter());
    all_locals
        .into_iter()
        .find(|l| l.id == id)
        .map(|l| ty_to_llvm(&l.ty))
        .unwrap_or("i64")
}

// ---------------------------------------------------------------------------
// Block label naming
// ---------------------------------------------------------------------------

/// Make a valid LLVM label from a block label string and block index.
fn block_label(block: &BasicBlock, idx: usize) -> String {
    let label = block.label.as_str();
    if label.is_empty() {
        format!("bb_{}", idx)
    } else {
        // Sanitize: replace non-alphanumeric with underscore
        let sanitized: String = label
            .chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect();
        format!("{}_{}", sanitized, idx)
    }
}

/// Build a map from BlockId → label name for a function.
fn build_block_labels(func: &Function) -> FxHashMap<BlockId, String> {
    let mut labels = FxHashMap::default();
    for (idx_counter, (id, block)) in func.basic_blocks.iter().enumerate() {
        labels.insert(id, block_label(block, idx_counter));
    }
    labels
}

// ---------------------------------------------------------------------------
// Function compilation
// ---------------------------------------------------------------------------

/// Compile a single MIR function to LLVM IR text.
fn compile_function(
    func: &Function,
    mir: &MirFile,
    ctx: &mut ModuleContext,
) -> Result<String, CodegenError> {
    let ret_ty = ty_to_llvm(&func.return_ty);
    let block_labels = build_block_labels(func);

    // Build parameter list
    let params: Vec<String> = func
        .params
        .iter()
        .enumerate()
        .map(|(i, local)| {
            let ty = ty_to_llvm(&local.ty);
            if ty == "void" {
                format!("i64 %arg.{}", i)
            } else {
                format!("{} %arg.{}", ty, i)
            }
        })
        .collect();

    let mut out = String::new();
    out.push_str(&format!(
        "define {} @{}({}) {{\n",
        ret_ty,
        func.name,
        params.join(", ")
    ));

    // Entry label
    out.push_str("entry:\n");

    let mut builder = IrBuilder::new();

    // Emit alloca for each parameter and local
    for (i, param) in func.params.iter().enumerate() {
        let ty = ty_to_llvm(&param.ty);
        let alloca_ty = if ty == "void" { "i64" } else { ty };
        let alloca_name = format!("%local.{}", param.id);
        builder.emit(&format!("{} = alloca {}", alloca_name, alloca_ty));
        let arg_ty = if ty == "void" { "i64" } else { ty };
        builder.emit(&format!("store {} %arg.{}, ptr {}", arg_ty, i, alloca_name));
        builder.local_alloca.insert(param.id, alloca_name);
    }
    for local in &func.locals {
        let ty = ty_to_llvm(&local.ty);
        let alloca_ty = if ty == "void" { "i64" } else { ty };
        let alloca_name = format!("%local.{}", local.id);
        builder.emit(&format!("{} = alloca {}", alloca_name, alloca_ty));
        builder.local_alloca.insert(local.id, alloca_name);
    }

    // Branch from entry to the first real block
    let entry_label = block_labels
        .get(&func.entry_block)
        .cloned()
        .unwrap_or_else(|| "bb_0".to_string());
    builder.emit(&format!("br label %{}", entry_label));

    // Append the entry alloca section to the output
    out.push_str(&builder.body);

    // Compile blocks in order: entry block first, then rest
    let mut block_order: Vec<BlockId> = Vec::new();
    block_order.push(func.entry_block);
    for (id, _) in func.basic_blocks.iter() {
        if id != func.entry_block {
            block_order.push(id);
        }
    }

    for &block_id in &block_order {
        let block = &func.basic_blocks[block_id];
        let label = block_labels
            .get(&block_id)
            .cloned()
            .unwrap_or_else(|| "bb_unknown".to_string());

        let mut bb_builder = IrBuilder {
            next_reg: builder.next_reg,
            body: String::new(),
            local_alloca: builder.local_alloca.clone(),
        };

        bb_builder.emit_label(&label);

        // Lower instructions
        for instr in &block.instructions {
            match &instr.kind {
                InstructionKind::Assign { target, value } => {
                    let val = lower_value(&mut bb_builder, value, func, mir, ctx)?;
                    let ty = local_ty(*target, func);
                    let store_ty = if ty == "void" { "i64" } else { ty };
                    let alloca_name = bb_builder
                        .local_alloca
                        .get(target)
                        .cloned()
                        .unwrap_or_else(|| format!("%local.{}", target));
                    bb_builder.emit(&format!("store {} {}, ptr {}", store_ty, val, alloca_name));
                }

                InstructionKind::Store { ptr, value } => {
                    let ptr_val = lower_value(&mut bb_builder, ptr, func, mir, ctx)?;
                    let val = lower_value(&mut bb_builder, value, func, mir, ctx)?;
                    let val_ty = infer_value_llvm_type(value, func, mir);
                    let store_ty = if val_ty == "void" { "i64" } else { val_ty };
                    bb_builder.emit(&format!("store {} {}, ptr {}", store_ty, val, ptr_val));
                }

                InstructionKind::Call {
                    target,
                    func: callee,
                    args,
                    ..
                } => {
                    // Lower arguments
                    let mut arg_strs: Vec<String> = Vec::new();
                    for arg in args.iter() {
                        let arg_val = lower_value(&mut bb_builder, arg, func, mir, ctx)?;
                        let arg_ty = infer_value_llvm_type(arg, func, mir);
                        let emit_ty = if arg_ty == "void" { "i64" } else { arg_ty };
                        arg_strs.push(format!("{} {}", emit_ty, arg_val));
                    }

                    // Resolve callee
                    let callee_name = match callee {
                        Value::Constant(id) => {
                            if let ConstantKind::Function(name) = &mir.constants[*id].kind {
                                format!("@{}", name)
                            } else {
                                "@__eclexia_unknown".to_string()
                            }
                        }
                        Value::Local(_id) => lower_value(&mut bb_builder, callee, func, mir, ctx)?,
                        _ => "@__eclexia_unknown".to_string(),
                    };

                    // Determine return type from target local (if any)
                    let call_ret_ty = if let Some(target_id) = target {
                        let ty = local_ty(*target_id, func);
                        if ty == "void" {
                            "i64"
                        } else {
                            ty
                        }
                    } else {
                        "void"
                    };

                    if let Some(target_id) = target {
                        let result_reg = bb_builder.fresh_reg();
                        bb_builder.emit(&format!(
                            "{} = call {} {}({})",
                            result_reg,
                            call_ret_ty,
                            callee_name,
                            arg_strs.join(", ")
                        ));
                        let alloca_name = bb_builder
                            .local_alloca
                            .get(target_id)
                            .cloned()
                            .unwrap_or_else(|| format!("%local.{}", target_id));
                        bb_builder.emit(&format!(
                            "store {} {}, ptr {}",
                            call_ret_ty, result_reg, alloca_name
                        ));
                    } else {
                        bb_builder.emit(&format!(
                            "call {} {}({})",
                            call_ret_ty,
                            callee_name,
                            arg_strs.join(", ")
                        ));
                    }
                }

                InstructionKind::ResourceTrack {
                    resource, amount, ..
                } => {
                    ctx.declare_extern("declare void @__eclexia_track_resource(ptr, double)");
                    let res_name = ctx.intern_string(resource.as_str());
                    let len = resource.len() + 1;
                    let str_reg = bb_builder.fresh_reg();
                    bb_builder.emit(&format!(
                        "{} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                        str_reg, len, res_name
                    ));
                    let amount_val = lower_value(&mut bb_builder, amount, func, mir, ctx)?;
                    bb_builder.emit(&format!(
                        "call void @__eclexia_track_resource(ptr {}, double {})",
                        str_reg, amount_val
                    ));
                }

                InstructionKind::ShadowPriceHook { resource, .. } => {
                    ctx.declare_extern("declare double @__eclexia_query_shadow_price(ptr)");
                    let res_name = ctx.intern_string(resource.as_str());
                    let len = resource.len() + 1;
                    let str_reg = bb_builder.fresh_reg();
                    bb_builder.emit(&format!(
                        "{} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                        str_reg, len, res_name
                    ));
                    let _result_reg = bb_builder.fresh_reg();
                    bb_builder.emit(&format!(
                        "{} = call double @__eclexia_query_shadow_price(ptr {})",
                        _result_reg, str_reg
                    ));
                }

                InstructionKind::Nop => {
                    bb_builder.emit("; nop");
                }
            }
        }

        // Lower terminator
        match &block.terminator {
            Terminator::Return(None) => {
                if ret_ty == "void" {
                    bb_builder.emit("ret void");
                } else {
                    // Return default zero value
                    bb_builder.emit(&format!("ret {} 0", ret_ty));
                }
            }
            Terminator::Return(Some(value)) => {
                let val = lower_value(&mut bb_builder, value, func, mir, ctx)?;
                if ret_ty == "void" {
                    bb_builder.emit("ret void");
                } else {
                    bb_builder.emit(&format!("ret {} {}", ret_ty, val));
                }
            }
            Terminator::Goto(target_block) => {
                let target_label = block_labels
                    .get(target_block)
                    .cloned()
                    .unwrap_or_else(|| "bb_unknown".to_string());
                bb_builder.emit(&format!("br label %{}", target_label));
            }
            Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => {
                let cond_val = lower_value(&mut bb_builder, condition, func, mir, ctx)?;
                let then_label = block_labels
                    .get(then_block)
                    .cloned()
                    .unwrap_or_else(|| "bb_then".to_string());
                let else_label = block_labels
                    .get(else_block)
                    .cloned()
                    .unwrap_or_else(|| "bb_else".to_string());
                bb_builder.emit(&format!(
                    "br i1 {}, label %{}, label %{}",
                    cond_val, then_label, else_label
                ));
            }
            Terminator::Switch {
                value,
                targets,
                default,
            } => {
                let val = lower_value(&mut bb_builder, value, func, mir, ctx)?;
                let val_ty = infer_value_llvm_type(value, func, mir);
                let switch_ty = if val_ty == "void" { "i64" } else { val_ty };
                let default_label = block_labels
                    .get(default)
                    .cloned()
                    .unwrap_or_else(|| "bb_default".to_string());
                let mut cases = String::new();
                for (case_val, target_block) in targets {
                    let target_label = block_labels
                        .get(target_block)
                        .cloned()
                        .unwrap_or_else(|| "bb_unknown".to_string());
                    cases.push_str(&format!(
                        "\n    {} {}, label %{}",
                        switch_ty, case_val, target_label
                    ));
                }
                bb_builder.emit(&format!(
                    "switch {} {}, label %{} [{}",
                    switch_ty, val, default_label, cases
                ));
                bb_builder.emit("]");
            }
            Terminator::Unreachable => {
                bb_builder.emit("unreachable");
            }
        }

        // Propagate register counter
        builder.next_reg = bb_builder.next_reg;
        out.push_str(&bb_builder.body);
    }

    out.push_str("}\n");
    Ok(out)
}

// ---------------------------------------------------------------------------
// Public API types
// ---------------------------------------------------------------------------

/// LLVM optimization level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptLevel {
    O0,
    O1,
    O2,
    O3,
}

impl OptLevel {
    /// Get a human-readable name.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::O0 => "O0",
            Self::O1 => "O1",
            Self::O2 => "O2",
            Self::O3 => "O3",
        }
    }
}

impl std::fmt::Display for OptLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-{}", self.as_str())
    }
}

/// LTO (Link-Time Optimization) mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LtoMode {
    /// No LTO.
    None,
    /// Thin LTO (faster, parallel).
    Thin,
    /// Full LTO (slower, better optimization).
    Full,
}

/// Output of the LLVM backend — contains generated LLVM IR text.
#[derive(Debug, Clone)]
pub struct LlvmModule {
    /// Optimization level used.
    pub opt_level: OptLevel,
    /// LTO mode used.
    pub lto_mode: LtoMode,
    /// Compiled functions (with IR sizes).
    pub functions: Vec<LlvmCompiledFunction>,
    /// Whether PGO data was used.
    pub pgo_used: bool,
    /// Total IR text size in bytes.
    pub estimated_code_size: usize,
    /// The complete LLVM IR module text.
    ir_text: String,
}

impl LlvmModule {
    /// Get the LLVM IR text.
    pub fn ir(&self) -> &str {
        &self.ir_text
    }

    /// Write the LLVM IR to a file.
    pub fn write_to_file(&self, path: &std::path::Path) -> std::io::Result<()> {
        std::fs::write(path, &self.ir_text)
    }

    /// Try to compile the IR with `llc` (if available on the system).
    pub fn compile_with_llc(
        &self,
        ll_path: &std::path::Path,
        output_path: &std::path::Path,
        opt_level: OptLevel,
    ) -> Result<(), String> {
        // Write IR to file first
        self.write_to_file(ll_path)
            .map_err(|e| format!("Failed to write IR: {}", e))?;

        let opt_flag = format!("-{}", opt_level.as_str());
        let status = std::process::Command::new("llc")
            .arg(&opt_flag)
            .arg("-filetype=obj")
            .arg(ll_path)
            .arg("-o")
            .arg(output_path)
            .status()
            .map_err(|e| format!("Failed to run llc: {}", e))?;

        if status.success() {
            Ok(())
        } else {
            Err(format!("llc exited with status: {}", status))
        }
    }
}

/// A compiled LLVM function.
#[derive(Debug, Clone)]
pub struct LlvmCompiledFunction {
    /// Function name.
    pub name: SmolStr,
    /// Size of the generated IR for this function (in bytes).
    pub ir_size: usize,
    /// Estimated native code size (rough heuristic).
    pub estimated_size: usize,
}

/// LLVM backend configuration.
pub struct LlvmBackend {
    opt_level: OptLevel,
    lto_mode: LtoMode,
    pgo_profile: Option<String>,
}

impl LlvmBackend {
    /// Create a new LLVM backend with default settings (O2, no LTO).
    pub fn new() -> Self {
        Self {
            opt_level: OptLevel::O2,
            lto_mode: LtoMode::None,
            pgo_profile: None,
        }
    }

    /// Create an LLVM backend for release builds (O3 + Thin LTO).
    pub fn release() -> Self {
        Self {
            opt_level: OptLevel::O3,
            lto_mode: LtoMode::Thin,
            pgo_profile: None,
        }
    }

    /// Set the optimization level.
    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    /// Set the LTO mode.
    pub fn with_lto(mut self, mode: LtoMode) -> Self {
        self.lto_mode = mode;
        self
    }

    /// Set the PGO profile path.
    pub fn with_pgo(mut self, profile_path: String) -> Self {
        self.pgo_profile = Some(profile_path);
        self
    }

    /// Get the optimization level.
    pub fn opt_level(&self) -> OptLevel {
        self.opt_level
    }

    /// Get the LTO mode.
    pub fn lto_mode(&self) -> LtoMode {
        self.lto_mode
    }
}

impl Default for LlvmBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for LlvmBackend {
    type Output = LlvmModule;

    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError> {
        let mut ctx = ModuleContext::new();

        // Register all functions
        for (i, func) in mir.functions.iter().enumerate() {
            ctx.register_function(func.name.clone(), i);
        }

        // Compile each function
        let mut function_irs: Vec<(SmolStr, String)> = Vec::new();
        for func in &mir.functions {
            let ir = compile_function(func, mir, &mut ctx)?;
            function_irs.push((func.name.clone(), ir));
        }

        // Assemble the complete module
        let mut module_ir = ctx.emit_header();
        module_ir.push_str(&ctx.emit_string_constants());
        module_ir.push_str(&ctx.emit_extern_decls());
        module_ir.push('\n');

        let mut functions = Vec::new();
        for (name, ir) in &function_irs {
            let ir_size = ir.len();
            // Rough native size estimate: ~1/4 of IR text size at O2
            let size_factor = match self.opt_level {
                OptLevel::O0 => 3,
                OptLevel::O1 => 4,
                OptLevel::O2 => 5,
                OptLevel::O3 => 6,
            };
            let estimated_size = ir_size / size_factor;

            functions.push(LlvmCompiledFunction {
                name: name.clone(),
                ir_size,
                estimated_size,
            });

            module_ir.push_str(ir);
            module_ir.push('\n');
        }

        let total_size = module_ir.len();

        Ok(LlvmModule {
            opt_level: self.opt_level,
            lto_mode: self.lto_mode,
            functions,
            pgo_used: self.pgo_profile.is_some(),
            estimated_code_size: total_size,
            ir_text: module_ir,
        })
    }

    fn name(&self) -> &str {
        "llvm"
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, ConstantKind, Function, Instruction, InstructionKind, Local,
        Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn zero_dim() -> Dimension {
        Dimension {
            mass: 0,
            length: 0,
            time: 0,
            current: 0,
            temperature: 0,
            amount: 0,
            luminosity: 0,
            money: 0,
            carbon: 0,
            information: 0,
        }
    }

    fn make_test_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![
                Instruction {
                    span: Span::new(0, 0),
                    kind: InstructionKind::Nop,
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
        let c_10 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(10),
        });
        let c_20 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(20),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Value::Constant(c_10)),
                        rhs: Box::new(Value::Constant(c_20)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("add_numbers"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Int),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::Int),
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

    fn make_float_arithmetic_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c_a = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(3.14),
        });
        let c_b = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(2.71),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Value::Constant(c_a)),
                        rhs: Box::new(Value::Constant(c_b)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("add_floats"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Float),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::Float),
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
            instructions: vec![Instruction {
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
                name: SmolStr::new("sum"),
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

    fn make_branch_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c_true = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Bool),
            kind: ConstantKind::Bool(true),
        });
        let c_1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(1),
        });
        let c_2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(2),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();

        let then_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("then"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Constant(c_1),
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let else_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("else"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Constant(c_2),
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("start"),
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
            return_ty: Ty::Primitive(PrimitiveTy::Int),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::Int),
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

    fn make_string_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c_hello = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::String),
            kind: ConstantKind::String(SmolStr::new("hello")),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Constant(c_hello),
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("get_string"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::String),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("s"),
                ty: Ty::Primitive(PrimitiveTy::String),
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

    fn make_resource_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c_amount = constants.alloc(Constant {
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
                    dimension: zero_dim(),
                    amount: Value::Constant(c_amount),
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("track_energy"),
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

    fn make_switch_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c_val = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(42),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();

        let case_a = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case_a"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_val))),
        });
        let case_b = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case_b"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_val))),
        });
        let default_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("default"),
            instructions: vec![],
            terminator: Terminator::Return(Some(Value::Constant(c_val))),
        });

        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Switch {
                value: Value::Constant(c_val),
                targets: vec![(1, case_a), (2, case_b)],
                default: default_block,
            },
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("switch_test"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Int),
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

    fn make_unreachable_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Unreachable,
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("never_returns"),
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

    // -----------------------------------------------------------------------
    // Original tests (updated for new struct fields)
    // -----------------------------------------------------------------------

    #[test]
    fn test_llvm_backend_name() {
        let backend = LlvmBackend::new();
        assert_eq!(backend.name(), "llvm");
    }

    #[test]
    fn test_llvm_generate() {
        let mut backend = LlvmBackend::new();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();

        assert_eq!(module.opt_level, OptLevel::O2);
        assert_eq!(module.lto_mode, LtoMode::None);
        assert_eq!(module.functions.len(), 1);
        assert!(!module.pgo_used);
        // Should contain real IR now
        assert!(module.ir().contains("define"));
    }

    #[test]
    fn test_llvm_release() {
        let mut backend = LlvmBackend::release();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();

        assert_eq!(module.opt_level, OptLevel::O3);
        assert_eq!(module.lto_mode, LtoMode::Thin);
    }

    #[test]
    fn test_llvm_with_pgo() {
        let mut backend = LlvmBackend::new().with_pgo("profile.eclprof".to_string());
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();

        assert!(module.pgo_used);
    }

    #[test]
    fn test_opt_level_display() {
        assert_eq!(format!("{}", OptLevel::O0), "-O0");
        assert_eq!(format!("{}", OptLevel::O3), "-O3");
    }

    #[test]
    fn test_empty_mir() {
        let mut backend = LlvmBackend::new();
        let mir = MirFile {
            functions: vec![],
            constants: Arena::new(),
        };
        let module = backend.generate(&mir).unwrap();
        assert!(module.functions.is_empty());
        // Should still have a valid module header
        assert!(module.ir().contains("ModuleID"));
    }

    // -----------------------------------------------------------------------
    // New tests for real IR generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_llvm_ir_contains_function_def() {
        let mut backend = LlvmBackend::new();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("define void @main()"));
        assert!(ir.contains("ret void"));
    }

    #[test]
    fn test_llvm_ir_arithmetic() {
        let mut backend = LlvmBackend::new();
        let mir = make_arithmetic_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("define i64 @add_numbers()"));
        assert!(ir.contains("add i64"));
        assert!(ir.contains("10"));
        assert!(ir.contains("20"));
        assert!(ir.contains("ret i64"));
    }

    #[test]
    fn test_llvm_ir_float_arithmetic() {
        let mut backend = LlvmBackend::new();
        let mir = make_float_arithmetic_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("define double @add_floats()"));
        assert!(ir.contains("fadd double"));
        assert!(ir.contains("ret double"));
    }

    #[test]
    fn test_llvm_ir_branch() {
        let mut backend = LlvmBackend::new();
        let mir = make_branch_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("br i1"));
        assert!(ir.contains("label %"));
        assert!(ir.contains("define i64 @branch_test()"));
    }

    #[test]
    fn test_llvm_ir_function_params() {
        let mut backend = LlvmBackend::new();
        let mir = make_params_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("define i64 @add(i64 %arg.0, i64 %arg.1)"));
        assert!(ir.contains("alloca i64"));
        assert!(ir.contains("store i64 %arg.0"));
        assert!(ir.contains("store i64 %arg.1"));
    }

    #[test]
    fn test_llvm_ir_string_constant() {
        let mut backend = LlvmBackend::new();
        let mir = make_string_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("@.str."));
        assert!(ir.contains("hello"));
        assert!(ir.contains("getelementptr"));
    }

    #[test]
    fn test_llvm_ir_resource_tracking() {
        let mut backend = LlvmBackend::new();
        let mir = make_resource_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("@__eclexia_track_resource"));
        assert!(ir.contains("declare void @__eclexia_track_resource(ptr, double)"));
        assert!(ir.contains("energy"));
    }

    #[test]
    fn test_llvm_ir_module_header() {
        let mut backend = LlvmBackend::new();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("target triple = \"x86_64-unknown-linux-gnu\""));
        assert!(ir.contains("target datalayout"));
        assert!(ir.contains("ModuleID"));
    }

    #[test]
    fn test_llvm_ir_switch() {
        let mut backend = LlvmBackend::new();
        let mir = make_switch_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("switch"));
        assert!(ir.contains("label %"));
    }

    #[test]
    fn test_llvm_ir_unreachable() {
        let mut backend = LlvmBackend::new();
        let mir = make_unreachable_mir();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("unreachable"));
    }

    #[test]
    fn test_format_float_hex() {
        // 0.0 should be 0x0000000000000000
        assert_eq!(format_float_hex(0.0), "0x0000000000000000");
        // 1.0 should be 0x3FF0000000000000
        assert_eq!(format_float_hex(1.0), "0x3FF0000000000000");
    }

    #[test]
    fn test_escape_llvm_string() {
        assert_eq!(escape_llvm_string("hello"), "hello");
        assert_eq!(escape_llvm_string("a\nb"), "a\\0Ab");
        assert_eq!(escape_llvm_string("a\"b"), "a\\22b");
    }

    #[test]
    fn test_type_mapping() {
        assert_eq!(prim_to_llvm(PrimitiveTy::Int), "i64");
        assert_eq!(prim_to_llvm(PrimitiveTy::I32), "i32");
        assert_eq!(prim_to_llvm(PrimitiveTy::Bool), "i1");
        assert_eq!(prim_to_llvm(PrimitiveTy::Float), "double");
        assert_eq!(prim_to_llvm(PrimitiveTy::F32), "float");
        assert_eq!(prim_to_llvm(PrimitiveTy::String), "ptr");
        assert_eq!(prim_to_llvm(PrimitiveTy::Unit), "void");
        assert_eq!(prim_to_llvm(PrimitiveTy::I8), "i8");
        assert_eq!(prim_to_llvm(PrimitiveTy::I16), "i16");
    }

    #[test]
    fn test_ir_accessor() {
        let mut backend = LlvmBackend::new();
        let mir = make_test_mir();
        let module = backend.generate(&mir).unwrap();
        // ir() should return the same content as the internal ir_text
        assert!(!module.ir().is_empty());
        assert!(module.estimated_code_size > 0);
    }

    #[test]
    fn test_shadow_price_hook() {
        let constants: Arena<Constant> = Arena::new();
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ShadowPriceHook {
                    resource: SmolStr::new("memory"),
                    dimension: zero_dim(),
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("check_shadow"),
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

        let mut backend = LlvmBackend::new();
        let module = backend.generate(&mir).unwrap();
        let ir = module.ir();

        assert!(ir.contains("@__eclexia_query_shadow_price"));
        assert!(ir.contains("declare double @__eclexia_query_shadow_price(ptr)"));
        assert!(ir.contains("memory"));
    }
}
