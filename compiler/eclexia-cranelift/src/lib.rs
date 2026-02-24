// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Cranelift native code backend for Eclexia.
//!
//! Generates native machine code using Cranelift for fast compilation.
//! Intended for development builds where compilation speed matters
//! more than peak runtime performance.
//!
//! ## Supported MIR lowering
//!
//! - Integer arithmetic (i32, i64): add, sub, mul, div, rem, pow, bitwise ops
//! - Float arithmetic (f32, f64): add, sub, mul, div, rem, pow, neg
//! - Comparisons (all types): eq, ne, lt, le, gt, ge
//! - Unary ops: neg, not, bitnot
//! - Constants: int, float, bool, char, unit, string (placeholder), function
//! - Locals: get, set
//! - Memory: load, store
//! - Control flow: return, goto, branch, switch, multi-block
//! - Function calls (direct and indirect)
//! - Resource tracking (ResourceTrack, ShadowPriceHook)
//! - Field/index access (base lowered)
//! - Nop passthrough
//!
//! ## Targets
//!
//! - x86_64 (primary, auto-detected via cranelift-native)
//! - aarch64 (ARM64)
//! - riscv64

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{
    AbiParam, ExtFuncData, ExternalName, FuncRef, Function as ClifFunc, InstBuilder, MemFlags,
    Signature, UserExternalName,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use eclexia_ast::types::{PrimitiveTy, Ty};
use eclexia_codegen::{Backend, CodegenError};
use eclexia_mir::{
    BinaryOp, BlockId, ConstantKind, InstructionKind, MirFile, Terminator, UnaryOp, Value,
};
use rustc_hash::FxHashMap;
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
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64"
        )))]
        {
            Self::X86_64
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
    /// String data section (constant strings used by functions).
    pub string_data: Vec<(String, Vec<u8>)>,
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
    /// Whether real native code was generated (vs. estimated).
    pub is_real_codegen: bool,
}

/// Map an Eclexia type to a Cranelift IR type.
fn ty_to_clif(ty: &Ty) -> Option<cranelift_codegen::ir::Type> {
    match ty {
        Ty::Primitive(p) => prim_to_clif(*p),
        Ty::Resource { base, .. } => prim_to_clif(*base),
        _ => None,
    }
}

/// Map an Eclexia primitive type to a Cranelift IR type.
fn prim_to_clif(p: PrimitiveTy) -> Option<cranelift_codegen::ir::Type> {
    match p {
        PrimitiveTy::Int | PrimitiveTy::I64 | PrimitiveTy::U64 => Some(types::I64),
        PrimitiveTy::I32 | PrimitiveTy::U32 | PrimitiveTy::Bool | PrimitiveTy::Char => {
            Some(types::I32)
        }
        PrimitiveTy::I8 | PrimitiveTy::U8 | PrimitiveTy::I16 | PrimitiveTy::U16 => Some(types::I32),
        PrimitiveTy::I128 | PrimitiveTy::U128 | PrimitiveTy::UInt => Some(types::I64),
        PrimitiveTy::Float | PrimitiveTy::F64 => Some(types::F64),
        PrimitiveTy::F32 => Some(types::F32),
        PrimitiveTy::String => Some(types::I64), // pointer
        PrimitiveTy::Unit => None,
    }
}

/// Check if a Cranelift type is a float type.
fn is_clif_float(ty: cranelift_codegen::ir::Type) -> bool {
    ty == types::F32 || ty == types::F64
}

/// Per-function compilation context mapping MIR constructs to CLIF.
struct FuncCtx {
    /// MIR block IDs → Cranelift blocks.
    clif_blocks: FxHashMap<BlockId, cranelift_codegen::ir::Block>,
    /// MIR function name → imported FuncRef (for cross-function calls).
    func_refs: FxHashMap<SmolStr, FuncRef>,
    /// Runtime helper: track_resource(resource_id: i64, amount: f64).
    track_resource_ref: Option<FuncRef>,
    /// Runtime helper: query_shadow_price(resource_id: i64) -> f64.
    query_shadow_price_ref: Option<FuncRef>,
    /// Runtime helper: pow(base: f64, exp: f64) -> f64.
    pow_ref: Option<FuncRef>,
    /// Runtime helper: fmod(x: f64, y: f64) -> f64.
    fmod_ref: Option<FuncRef>,
}

/// Ensure a value is i8 for use in `brif`. Cranelift `brif` expects an i8 condition.
fn ensure_i8_bool(
    val: cranelift_codegen::ir::Value,
    builder: &mut FunctionBuilder,
) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I8 {
        val
    } else {
        builder.ins().icmp_imm(IntCC::NotEqual, val, 0)
    }
}

/// Simple hash for resource names → i64 identifier (for runtime helper calls).
fn hash_resource_name(name: &str) -> i64 {
    let mut h: u64 = 5381;
    for b in name.bytes() {
        h = h.wrapping_mul(33).wrapping_add(b as u64);
    }
    h as i64
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

    /// Compile a MIR function using real Cranelift codegen.
    /// Returns Some(code_size) on success, None if unsupported constructs are encountered.
    fn try_real_compile(&self, func: &eclexia_mir::Function, mir: &MirFile) -> Option<usize> {
        // Build Cranelift ISA for the host
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").ok()?;
        let flags = settings::Flags::new(flag_builder);

        let isa = cranelift_native::builder().ok()?.finish(flags).ok()?;

        // Build function signature
        let mut sig = Signature::new(CallConv::SystemV);

        for param in &func.params {
            let clif_ty = ty_to_clif(&param.ty)?;
            sig.params.push(AbiParam::new(clif_ty));
        }

        if let Some(ret_ty) = ty_to_clif(&func.return_ty) {
            sig.returns.push(AbiParam::new(ret_ty));
        }

        // Create function
        let mut clif_func = ClifFunc::new();
        clif_func.signature = sig;

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut clif_func, &mut builder_ctx);

        // --- Build FuncCtx: import all needed function signatures ---
        let mut ctx = FuncCtx {
            clif_blocks: FxHashMap::default(),
            func_refs: FxHashMap::default(),
            track_resource_ref: None,
            query_shadow_price_ref: None,
            pow_ref: None,
            fmod_ref: None,
        };

        // Import signatures for all MIR functions (for cross-function calls).
        // Each gets ExternalName::user() with a UserExternalName in namespace 0.
        for (idx, mir_func) in mir.functions.iter().enumerate() {
            let mut callee_sig = Signature::new(CallConv::SystemV);
            for p in &mir_func.params {
                if let Some(ct) = ty_to_clif(&p.ty) {
                    callee_sig.params.push(AbiParam::new(ct));
                }
            }
            if let Some(rt) = ty_to_clif(&mir_func.return_ty) {
                callee_sig.returns.push(AbiParam::new(rt));
            }
            let sig_ref = builder.import_signature(callee_sig);
            let user_name = UserExternalName {
                namespace: 0,
                index: idx as u32,
            };
            let name_ref = builder.func.declare_imported_user_function(user_name);
            let func_ref = builder.import_function(ExtFuncData {
                name: ExternalName::user(name_ref),
                signature: sig_ref,
                colocated: false,
            });
            ctx.func_refs.insert(mir_func.name.clone(), func_ref);
        }

        // Import runtime helpers in namespace 1.
        // track_resource(resource_id: i64, amount: f64) -> void
        {
            let mut s = Signature::new(CallConv::SystemV);
            s.params.push(AbiParam::new(types::I64));
            s.params.push(AbiParam::new(types::F64));
            let sr = builder.import_signature(s);
            let nr = builder
                .func
                .declare_imported_user_function(UserExternalName {
                    namespace: 1,
                    index: 0,
                });
            ctx.track_resource_ref = Some(builder.import_function(ExtFuncData {
                name: ExternalName::user(nr),
                signature: sr,
                colocated: false,
            }));
        }
        // query_shadow_price(resource_id: i64) -> f64
        {
            let mut s = Signature::new(CallConv::SystemV);
            s.params.push(AbiParam::new(types::I64));
            s.returns.push(AbiParam::new(types::F64));
            let sr = builder.import_signature(s);
            let nr = builder
                .func
                .declare_imported_user_function(UserExternalName {
                    namespace: 1,
                    index: 1,
                });
            ctx.query_shadow_price_ref = Some(builder.import_function(ExtFuncData {
                name: ExternalName::user(nr),
                signature: sr,
                colocated: false,
            }));
        }
        // pow(base: f64, exp: f64) -> f64
        {
            let mut s = Signature::new(CallConv::SystemV);
            s.params.push(AbiParam::new(types::F64));
            s.params.push(AbiParam::new(types::F64));
            s.returns.push(AbiParam::new(types::F64));
            let sr = builder.import_signature(s);
            let nr = builder
                .func
                .declare_imported_user_function(UserExternalName {
                    namespace: 1,
                    index: 2,
                });
            ctx.pow_ref = Some(builder.import_function(ExtFuncData {
                name: ExternalName::user(nr),
                signature: sr,
                colocated: false,
            }));
        }
        // fmod(x: f64, y: f64) -> f64
        {
            let mut s = Signature::new(CallConv::SystemV);
            s.params.push(AbiParam::new(types::F64));
            s.params.push(AbiParam::new(types::F64));
            s.returns.push(AbiParam::new(types::F64));
            let sr = builder.import_signature(s);
            let nr = builder
                .func
                .declare_imported_user_function(UserExternalName {
                    namespace: 1,
                    index: 3,
                });
            ctx.fmod_ref = Some(builder.import_function(ExtFuncData {
                name: ExternalName::user(nr),
                signature: sr,
                colocated: false,
            }));
        }

        // --- Create CLIF blocks for every MIR basic block ---
        // Gather block IDs: entry first, then rest in arena order.
        let mut block_ids: Vec<BlockId> = Vec::new();
        block_ids.push(func.entry_block);
        for (id, _) in func.basic_blocks.iter() {
            if id != func.entry_block {
                block_ids.push(id);
            }
        }

        // Create a CLIF block for each MIR block.
        for &bid in &block_ids {
            let clif_block = builder.create_block();
            ctx.clif_blocks.insert(bid, clif_block);
        }

        // Entry block gets function params.
        let entry_clif = ctx.clif_blocks[&func.entry_block];
        builder.append_block_params_for_function_params(entry_clif);

        // Declare all variables (params + locals) — must happen before any block.
        for param in &func.params {
            let var = Variable::from_u32(param.id);
            let clif_ty = ty_to_clif(&param.ty)?;
            builder.declare_var(var, clif_ty);
        }
        for local in &func.locals {
            let var = Variable::from_u32(local.id);
            let clif_ty = ty_to_clif(&local.ty)?;
            builder.declare_var(var, clif_ty);
        }

        // --- Process each block ---
        for &bid in &block_ids {
            let clif_block = ctx.clif_blocks[&bid];
            builder.switch_to_block(clif_block);

            // Bind params for entry block only.
            if bid == func.entry_block {
                for (i, param) in func.params.iter().enumerate() {
                    let var = Variable::from_u32(param.id);
                    let block_param = builder.block_params(entry_clif)[i];
                    builder.def_var(var, block_param);
                }
            }

            let bb = &func.basic_blocks[bid];

            // Lower instructions.
            for instr in &bb.instructions {
                if !self.lower_instruction_cranelift(&instr.kind, &mut builder, func, mir, &ctx)? {
                    return None;
                }
            }

            // Lower terminator.
            self.lower_terminator_cranelift(&bb.terminator, &mut builder, func, mir, &ctx)?;
        }

        builder.seal_all_blocks();
        builder.finalize();

        // Compile with Cranelift
        let mut compile_ctx = Context::for_function(clif_func);
        compile_ctx.compile(&*isa, &mut Default::default()).ok()?;

        compile_ctx
            .compiled_code()
            .map(|code| code.code_buffer().len())
    }

    /// Lower a MIR instruction to Cranelift IR.
    /// Returns Some(true) on success, Some(false) to skip, None on unsupported.
    fn lower_instruction_cranelift(
        &self,
        kind: &InstructionKind,
        builder: &mut FunctionBuilder,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        ctx: &FuncCtx,
    ) -> Option<bool> {
        match kind {
            InstructionKind::Assign { target, value } => {
                let val = self.lower_value_cranelift(value, builder, func, mir, ctx)?;
                let var = Variable::from_u32(*target);
                builder.def_var(var, val);
                Some(true)
            }
            InstructionKind::Nop => Some(true),
            InstructionKind::Store { ptr, value } => {
                let ptr_val = self.lower_value_cranelift(ptr, builder, func, mir, ctx)?;
                let data_val = self.lower_value_cranelift(value, builder, func, mir, ctx)?;
                builder.ins().store(MemFlags::new(), data_val, ptr_val, 0);
                Some(true)
            }
            InstructionKind::Call {
                target,
                func: callee,
                args,
                ..
            } => {
                // Lower all arguments.
                let mut arg_vals = Vec::with_capacity(args.len());
                for arg in args {
                    arg_vals.push(self.lower_value_cranelift(arg, builder, func, mir, ctx)?);
                }

                // Resolve callee. If it's a Constant(Function(name)), use the imported
                // FuncRef; otherwise emit an indirect call.
                let call_inst = if let Value::Constant(cid) = callee {
                    let constant = &mir.constants[*cid];
                    if let ConstantKind::Function(name) = &constant.kind {
                        if let Some(&fref) = ctx.func_refs.get(name.as_str()) {
                            builder.ins().call(fref, &arg_vals)
                        } else {
                            // Unknown function — still emit a call via the first func_ref
                            // as a placeholder (generates valid IR with relocation).
                            let fref = *ctx.func_refs.values().next()?;
                            builder.ins().call(fref, &arg_vals)
                        }
                    } else {
                        // Non-function constant used as callee — treat as indirect.
                        let callee_val =
                            self.lower_value_cranelift(callee, builder, func, mir, ctx)?;
                        let callee_sig = builder.func.dfg.signatures.keys().next()?;
                        builder
                            .ins()
                            .call_indirect(callee_sig, callee_val, &arg_vals)
                    }
                } else {
                    // Indirect call via a computed value.
                    let callee_val = self.lower_value_cranelift(callee, builder, func, mir, ctx)?;
                    let callee_sig = builder.func.dfg.signatures.keys().next()?;
                    builder
                        .ins()
                        .call_indirect(callee_sig, callee_val, &arg_vals)
                };

                // Bind result to target local if present.
                if let Some(tgt) = target {
                    let results = builder.inst_results(call_inst);
                    if let Some(&res) = results.first() {
                        let var = Variable::from_u32(*tgt);
                        builder.def_var(var, res);
                    }
                }
                Some(true)
            }
            InstructionKind::ResourceTrack {
                resource, amount, ..
            } => {
                let amount_val = self.lower_value_cranelift(amount, builder, func, mir, ctx)?;
                // Convert amount to f64 if needed.
                let amount_f64 = {
                    let ty = builder.func.dfg.value_type(amount_val);
                    if ty == types::F64 {
                        amount_val
                    } else if is_clif_float(ty) {
                        builder.ins().fpromote(types::F64, amount_val)
                    } else {
                        builder.ins().fcvt_from_sint(types::F64, amount_val)
                    }
                };
                let resource_id = builder
                    .ins()
                    .iconst(types::I64, hash_resource_name(resource.as_str()));
                if let Some(fref) = ctx.track_resource_ref {
                    builder.ins().call(fref, &[resource_id, amount_f64]);
                }
                Some(true)
            }
            InstructionKind::ShadowPriceHook { resource, .. } => {
                let resource_id = builder
                    .ins()
                    .iconst(types::I64, hash_resource_name(resource.as_str()));
                if let Some(fref) = ctx.query_shadow_price_ref {
                    builder.ins().call(fref, &[resource_id]);
                }
                Some(true)
            }
        }
    }

    /// Lower a MIR terminator to Cranelift IR.
    fn lower_terminator_cranelift(
        &self,
        term: &Terminator,
        builder: &mut FunctionBuilder,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        ctx: &FuncCtx,
    ) -> Option<()> {
        match term {
            Terminator::Return(None) => {
                builder.ins().return_(&[]);
                Some(())
            }
            Terminator::Return(Some(value)) => {
                let val = self.lower_value_cranelift(value, builder, func, mir, ctx)?;
                builder.ins().return_(&[val]);
                Some(())
            }
            Terminator::Unreachable => {
                let trap_code = cranelift_codegen::ir::TrapCode::user(0)
                    .unwrap_or(cranelift_codegen::ir::TrapCode::STACK_OVERFLOW);
                builder.ins().trap(trap_code);
                Some(())
            }
            Terminator::Goto(target) => {
                let clif_block = *ctx.clif_blocks.get(target)?;
                builder.ins().jump(clif_block, &[]);
                Some(())
            }
            Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => {
                let cond = self.lower_value_cranelift(condition, builder, func, mir, ctx)?;
                let cond_i8 = ensure_i8_bool(cond, builder);
                let then_clif = *ctx.clif_blocks.get(then_block)?;
                let else_clif = *ctx.clif_blocks.get(else_block)?;
                builder.ins().brif(cond_i8, then_clif, &[], else_clif, &[]);
                Some(())
            }
            Terminator::Switch {
                value,
                targets,
                default,
            } => {
                let val = self.lower_value_cranelift(value, builder, func, mir, ctx)?;
                let default_clif = *ctx.clif_blocks.get(default)?;
                let mut switch = cranelift_frontend::Switch::new();
                for &(case_val, ref target_bid) in targets {
                    let target_clif = *ctx.clif_blocks.get(target_bid)?;
                    switch.set_entry(case_val as u128, target_clif);
                }
                switch.emit(builder, val, default_clif);
                Some(())
            }
        }
    }

    /// Lower a MIR Value to a Cranelift IR value.
    #[allow(clippy::only_used_in_recursion)]
    fn lower_value_cranelift(
        &self,
        value: &Value,
        builder: &mut FunctionBuilder,
        func: &eclexia_mir::Function,
        mir: &MirFile,
        ctx: &FuncCtx,
    ) -> Option<cranelift_codegen::ir::Value> {
        match value {
            Value::Local(id) => {
                let var = Variable::from_u32(*id);
                Some(builder.use_var(var))
            }
            Value::Constant(id) => {
                let constant = &mir.constants[*id];
                match &constant.kind {
                    ConstantKind::Int(n) => {
                        let clif_ty = ty_to_clif(&constant.ty).unwrap_or(types::I64);
                        if clif_ty == types::I32 {
                            Some(builder.ins().iconst(types::I32, *n))
                        } else {
                            Some(builder.ins().iconst(types::I64, *n))
                        }
                    }
                    ConstantKind::Float(f) => {
                        let clif_ty = ty_to_clif(&constant.ty).unwrap_or(types::F64);
                        if clif_ty == types::F32 {
                            Some(builder.ins().f32const(*f as f32))
                        } else {
                            Some(builder.ins().f64const(*f))
                        }
                    }
                    ConstantKind::Bool(b) => Some(builder.ins().iconst(types::I32, *b as i64)),
                    ConstantKind::Char(c) => Some(builder.ins().iconst(types::I32, *c as i64)),
                    ConstantKind::Unit => {
                        // Unit has no value — but if someone tries to use it,
                        // return a zero i32 as a placeholder
                        Some(builder.ins().iconst(types::I32, 0))
                    }
                    ConstantKind::Resource { value, .. } => Some(builder.ins().f64const(*value)),
                    ConstantKind::String(s) => {
                        // TODO: Real implementation requires:
                        // 1. Add string to module-level data section (NativeModule.string_data)
                        // 2. Create a data object in the object file
                        // 3. Use symbol_value() to reference the data object
                        // 4. Return pointer to the string data
                        //
                        // For now: return a non-zero placeholder address
                        // The hash serves as a unique identifier for this string
                        let placeholder_addr = hash_resource_name(s) & 0x7FFFFFFF;
                        Some(builder.ins().iconst(types::I64, placeholder_addr))
                    }
                    ConstantKind::Function(name) => {
                        if let Some(&fref) = ctx.func_refs.get(name.as_str()) {
                            Some(builder.ins().func_addr(types::I64, fref))
                        } else {
                            // Unknown function — return null pointer placeholder.
                            Some(builder.ins().iconst(types::I64, 0))
                        }
                    }
                }
            }
            Value::Binary { op, lhs, rhs } => {
                let lhs_val = self.lower_value_cranelift(lhs, builder, func, mir, ctx)?;
                let rhs_val = self.lower_value_cranelift(rhs, builder, func, mir, ctx)?;

                // Detect the type from the Cranelift value
                let lhs_ty = builder.func.dfg.value_type(lhs_val);
                let is_float = is_clif_float(lhs_ty);

                if is_float {
                    self.lower_float_binop(*op, lhs_val, rhs_val, builder, ctx)
                } else {
                    self.lower_int_binop(*op, lhs_val, rhs_val, lhs_ty, builder, ctx)
                }
            }
            Value::Unary { op, operand } => {
                let val = self.lower_value_cranelift(operand, builder, func, mir, ctx)?;
                let val_ty = builder.func.dfg.value_type(val);
                let is_float = is_clif_float(val_ty);

                match op {
                    UnaryOp::Neg if is_float => Some(builder.ins().fneg(val)),
                    UnaryOp::Neg => Some(builder.ins().ineg(val)),
                    UnaryOp::Not => {
                        // Logical NOT: val == 0
                        let zero = builder.ins().iconst(val_ty, 0);
                        let cmp = builder.ins().icmp(IntCC::Equal, val, zero);
                        // icmp returns I8, extend to I32
                        Some(builder.ins().uextend(types::I32, cmp))
                    }
                    UnaryOp::BitNot => Some(builder.ins().bnot(val)),
                }
            }
            Value::Cast { value, target_ty } => {
                let val = self.lower_value_cranelift(value, builder, func, mir, ctx)?;
                let src_ty = builder.func.dfg.value_type(val);
                let dst_ty = ty_to_clif(target_ty)?;

                if src_ty == dst_ty {
                    return Some(val);
                }

                // Int → larger int
                if !is_clif_float(src_ty) && !is_clif_float(dst_ty) {
                    if src_ty.bits() < dst_ty.bits() {
                        return Some(builder.ins().sextend(dst_ty, val));
                    } else {
                        return Some(builder.ins().ireduce(dst_ty, val));
                    }
                }

                // Int → float
                if !is_clif_float(src_ty) && is_clif_float(dst_ty) {
                    return Some(builder.ins().fcvt_from_sint(dst_ty, val));
                }

                // Float → int
                if is_clif_float(src_ty) && !is_clif_float(dst_ty) {
                    return Some(builder.ins().fcvt_to_sint_sat(dst_ty, val));
                }

                // Float → float (f32 ↔ f64)
                if src_ty == types::F32 && dst_ty == types::F64 {
                    return Some(builder.ins().fpromote(types::F64, val));
                }
                if src_ty == types::F64 && dst_ty == types::F32 {
                    return Some(builder.ins().fdemote(types::F32, val));
                }

                None
            }
            Value::Load { ptr } => {
                let ptr_val = self.lower_value_cranelift(ptr, builder, func, mir, ctx)?;
                Some(builder.ins().load(types::I64, MemFlags::new(), ptr_val, 0))
            }
            Value::Field { base, .. } | Value::Index { base, .. } => {
                // Partial support: lower the base expression (same approach as WASM/LLVM).
                self.lower_value_cranelift(base, builder, func, mir, ctx)
            }
        }
    }

    /// Lower a float binary operation.
    fn lower_float_binop(
        &self,
        op: BinaryOp,
        lhs: cranelift_codegen::ir::Value,
        rhs: cranelift_codegen::ir::Value,
        builder: &mut FunctionBuilder,
        ctx: &FuncCtx,
    ) -> Option<cranelift_codegen::ir::Value> {
        use cranelift_codegen::ir::condcodes::FloatCC;
        match op {
            BinaryOp::Add => Some(builder.ins().fadd(lhs, rhs)),
            BinaryOp::Sub => Some(builder.ins().fsub(lhs, rhs)),
            BinaryOp::Mul => Some(builder.ins().fmul(lhs, rhs)),
            BinaryOp::Div => Some(builder.ins().fdiv(lhs, rhs)),
            BinaryOp::Rem => {
                // Float remainder: call imported fmod(x, y) -> f64.
                // Promote to f64 if f32, call fmod, demote back if needed.
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let (lhs_f64, rhs_f64) = if lhs_ty == types::F32 {
                    (
                        builder.ins().fpromote(types::F64, lhs),
                        builder.ins().fpromote(types::F64, rhs),
                    )
                } else {
                    (lhs, rhs)
                };
                let fref = ctx.fmod_ref?;
                let call = builder.ins().call(fref, &[lhs_f64, rhs_f64]);
                let result = builder.inst_results(call)[0];
                if lhs_ty == types::F32 {
                    Some(builder.ins().fdemote(types::F32, result))
                } else {
                    Some(result)
                }
            }
            BinaryOp::Pow => {
                // Float pow: call imported pow(base, exp) -> f64.
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let (lhs_f64, rhs_f64) = if lhs_ty == types::F32 {
                    (
                        builder.ins().fpromote(types::F64, lhs),
                        builder.ins().fpromote(types::F64, rhs),
                    )
                } else {
                    (lhs, rhs)
                };
                let fref = ctx.pow_ref?;
                let call = builder.ins().call(fref, &[lhs_f64, rhs_f64]);
                let result = builder.inst_results(call)[0];
                if lhs_ty == types::F32 {
                    Some(builder.ins().fdemote(types::F32, result))
                } else {
                    Some(result)
                }
            }
            // Logical ops on floats: compare != 0 to get int, apply, convert back.
            BinaryOp::And | BinaryOp::Or => {
                // For floats, logical AND/OR: return lhs as reasonable fallback.
                Some(lhs)
            }
            // Bitwise ops on floats: bitcast to int, apply, bitcast back.
            BinaryOp::BitAnd => {
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let int_ty = if lhs_ty == types::F32 {
                    types::I32
                } else {
                    types::I64
                };
                let li = builder.ins().bitcast(int_ty, MemFlags::new(), lhs);
                let ri = builder.ins().bitcast(int_ty, MemFlags::new(), rhs);
                let res = builder.ins().band(li, ri);
                Some(builder.ins().bitcast(lhs_ty, MemFlags::new(), res))
            }
            BinaryOp::BitOr => {
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let int_ty = if lhs_ty == types::F32 {
                    types::I32
                } else {
                    types::I64
                };
                let li = builder.ins().bitcast(int_ty, MemFlags::new(), lhs);
                let ri = builder.ins().bitcast(int_ty, MemFlags::new(), rhs);
                let res = builder.ins().bor(li, ri);
                Some(builder.ins().bitcast(lhs_ty, MemFlags::new(), res))
            }
            BinaryOp::BitXor => {
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let int_ty = if lhs_ty == types::F32 {
                    types::I32
                } else {
                    types::I64
                };
                let li = builder.ins().bitcast(int_ty, MemFlags::new(), lhs);
                let ri = builder.ins().bitcast(int_ty, MemFlags::new(), rhs);
                let res = builder.ins().bxor(li, ri);
                Some(builder.ins().bitcast(lhs_ty, MemFlags::new(), res))
            }
            BinaryOp::Shl => {
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let int_ty = if lhs_ty == types::F32 {
                    types::I32
                } else {
                    types::I64
                };
                let li = builder.ins().bitcast(int_ty, MemFlags::new(), lhs);
                let ri = builder.ins().bitcast(int_ty, MemFlags::new(), rhs);
                let res = builder.ins().ishl(li, ri);
                Some(builder.ins().bitcast(lhs_ty, MemFlags::new(), res))
            }
            BinaryOp::Shr => {
                let lhs_ty = builder.func.dfg.value_type(lhs);
                let int_ty = if lhs_ty == types::F32 {
                    types::I32
                } else {
                    types::I64
                };
                let li = builder.ins().bitcast(int_ty, MemFlags::new(), lhs);
                let ri = builder.ins().bitcast(int_ty, MemFlags::new(), rhs);
                let res = builder.ins().sshr(li, ri);
                Some(builder.ins().bitcast(lhs_ty, MemFlags::new(), res))
            }
            // Range/RangeInclusive: TODO - proper implementation requires:
            // 1. Allocate stack slot for {start: i64, end: i64} struct
            // 2. Store lhs to start field, rhs to end field
            // 3. Return pointer to the stack slot
            // For now: return placeholder (ideally would be struct pointer)
            BinaryOp::Range | BinaryOp::RangeInclusive => Some(builder.ins().iconst(types::I64, 0)),
            // Float comparisons → i32 result
            BinaryOp::Eq => {
                let cmp = builder.ins().fcmp(FloatCC::Equal, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Ne => {
                let cmp = builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Lt => {
                let cmp = builder.ins().fcmp(FloatCC::LessThan, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Le => {
                let cmp = builder.ins().fcmp(FloatCC::LessThanOrEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Gt => {
                let cmp = builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Ge => {
                let cmp = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
        }
    }

    /// Lower an integer binary operation.
    fn lower_int_binop(
        &self,
        op: BinaryOp,
        lhs: cranelift_codegen::ir::Value,
        rhs: cranelift_codegen::ir::Value,
        ty: cranelift_codegen::ir::Type,
        builder: &mut FunctionBuilder,
        ctx: &FuncCtx,
    ) -> Option<cranelift_codegen::ir::Value> {
        match op {
            BinaryOp::Add => Some(builder.ins().iadd(lhs, rhs)),
            BinaryOp::Sub => Some(builder.ins().isub(lhs, rhs)),
            BinaryOp::Mul => Some(builder.ins().imul(lhs, rhs)),
            BinaryOp::Div => Some(builder.ins().sdiv(lhs, rhs)),
            BinaryOp::Rem => Some(builder.ins().srem(lhs, rhs)),
            BinaryOp::Pow => {
                // Integer pow: convert to f64, call pow, convert back.
                let lhs_f64 = builder.ins().fcvt_from_sint(types::F64, lhs);
                let rhs_f64 = builder.ins().fcvt_from_sint(types::F64, rhs);
                let fref = ctx.pow_ref?;
                let call = builder.ins().call(fref, &[lhs_f64, rhs_f64]);
                let result_f64 = builder.inst_results(call)[0];
                Some(builder.ins().fcvt_to_sint_sat(ty, result_f64))
            }
            BinaryOp::BitAnd | BinaryOp::And => Some(builder.ins().band(lhs, rhs)),
            BinaryOp::BitOr | BinaryOp::Or => Some(builder.ins().bor(lhs, rhs)),
            BinaryOp::BitXor => Some(builder.ins().bxor(lhs, rhs)),
            BinaryOp::Shl => Some(builder.ins().ishl(lhs, rhs)),
            BinaryOp::Shr => Some(builder.ins().sshr(lhs, rhs)),
            // Range/RangeInclusive: TODO - proper implementation requires:
            // 1. Allocate stack slot for {start: i64, end: i64} struct
            // 2. Store lhs to start field, rhs to end field
            // 3. Return pointer to the stack slot
            // For now: return placeholder (ideally would be struct pointer)
            BinaryOp::Range | BinaryOp::RangeInclusive => Some(builder.ins().iconst(types::I64, 0)),
            // Integer comparisons → i32 result
            BinaryOp::Eq => {
                let cmp = builder.ins().icmp(IntCC::Equal, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Ne => {
                let cmp = builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Lt => {
                let cmp = builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Le => {
                let cmp = builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Gt => {
                let cmp = builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
            BinaryOp::Ge => {
                let cmp = builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
                Some(builder.ins().uextend(types::I32, cmp))
            }
        }
    }

    /// Estimate code size for functions we can't compile with real Cranelift yet.
    fn estimate_code_size(func: &eclexia_mir::Function) -> usize {
        let instr_count: usize = func
            .basic_blocks
            .iter()
            .map(|(_, block)| block.instructions.len())
            .sum();

        (instr_count + 2) * 8
    }

    /// Compile a single MIR function.
    fn compile_function(
        &self,
        func: &eclexia_mir::Function,
        mir: &MirFile,
    ) -> Result<CompiledFunction, CodegenError> {
        let has_resource_tracking = func.basic_blocks.iter().any(|(_, block)| {
            block
                .instructions
                .iter()
                .any(|i| matches!(i.kind, InstructionKind::ResourceTrack { .. }))
        });

        // Try real Cranelift compilation
        if let Some(real_size) = self.try_real_compile(func, mir) {
            return Ok(CompiledFunction {
                name: func.name.clone(),
                code_size: real_size,
                has_resource_tracking,
                is_real_codegen: true,
            });
        }

        // Fall back to size estimation
        Ok(CompiledFunction {
            name: func.name.clone(),
            code_size: Self::estimate_code_size(func),
            has_resource_tracking,
            is_real_codegen: false,
        })
    }
}

impl Backend for CraneliftBackend {
    type Output = NativeModule;

    fn generate(&mut self, mir: &MirFile) -> Result<Self::Output, CodegenError> {
        let mut functions = Vec::new();
        let mut total_code_size = 0;

        for func in &mir.functions {
            let compiled = self.compile_function(func, mir)?;
            total_code_size += compiled.code_size;
            functions.push(compiled);
        }

        // TODO: Collect string constants during lowering and add to string_data
        // For now, placeholder empty data section
        let string_data = Vec::new();

        Ok(NativeModule {
            target: self.target,
            functions,
            total_code_size,
            string_data,
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
    use eclexia_mir::{BasicBlock, Constant, Function, Instruction, Local, ResourceConstraint};
    use la_arena::Arena;

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

    fn make_resource_mir() -> MirFile {
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

    fn make_simple_void_mir() -> MirFile {
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
            name: SmolStr::new("noop"),
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

    fn make_int_arithmetic_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(42),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(10),
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
                        lhs: Box::new(Value::Constant(c1)),
                        rhs: Box::new(Value::Constant(c2)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("add_ints"),
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

    fn make_float_arithmetic_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::F64),
            kind: ConstantKind::Float(3.14),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::F64),
            kind: ConstantKind::Float(2.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Mul,
                        lhs: Box::new(Value::Constant(c1)),
                        rhs: Box::new(Value::Constant(c2)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("mul_floats"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::F64),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::F64),
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

    fn make_comparison_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(5),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(10),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Binary {
                        op: BinaryOp::Lt,
                        lhs: Box::new(Value::Constant(c1)),
                        rhs: Box::new(Value::Constant(c2)),
                    },
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("is_less"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I32),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("result"),
                ty: Ty::Primitive(PrimitiveTy::I32),
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
    fn test_cranelift_backend_name() {
        let backend = CraneliftBackend::host();
        assert_eq!(backend.name(), "cranelift");
    }

    #[test]
    fn test_cranelift_generate_with_resources() {
        let mut backend = CraneliftBackend::host();
        let mir = make_resource_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "main");
        assert!(module.functions[0].has_resource_tracking);
        assert!(
            module.functions[0].is_real_codegen,
            "Resource functions now compile to real codegen"
        );
        assert!(module.total_code_size > 0);
    }

    #[test]
    fn test_native_target_triple() {
        assert_eq!(NativeTarget::X86_64.triple(), "x86_64-unknown-linux-gnu");
        assert_eq!(NativeTarget::Aarch64.triple(), "aarch64-unknown-linux-gnu");
        assert_eq!(
            NativeTarget::Riscv64.triple(),
            "riscv64gc-unknown-linux-gnu"
        );
    }

    #[test]
    fn test_native_target_host() {
        assert_eq!(NativeTarget::host(), NativeTarget::X86_64);
    }

    #[test]
    fn test_cranelift_empty_mir() {
        let mut backend = CraneliftBackend::host();
        let mir = MirFile {
            functions: vec![],
            constants: Arena::new(),
        };
        let module = backend.generate(&mir).unwrap_ok();
        assert!(module.functions.is_empty());
        assert_eq!(module.total_code_size, 0);
    }

    #[test]
    fn test_native_target_display() {
        assert_eq!(
            format!("{}", NativeTarget::X86_64),
            "x86_64-unknown-linux-gnu"
        );
    }

    #[test]
    fn test_cranelift_real_compile_void() {
        let mut backend = CraneliftBackend::host();
        let mir = make_simple_void_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Simple void function should use real codegen"
        );
        assert!(module.functions[0].code_size > 0);
    }

    #[test]
    fn test_cranelift_real_compile_int_arithmetic() {
        let mut backend = CraneliftBackend::host();
        let mir = make_int_arithmetic_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Int arithmetic should use real codegen"
        );
        assert!(module.functions[0].code_size > 0);
    }

    #[test]
    fn test_cranelift_real_compile_float_arithmetic() {
        let mut backend = CraneliftBackend::host();
        let mir = make_float_arithmetic_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Float arithmetic should use real codegen"
        );
        assert!(module.functions[0].code_size > 0);
    }

    #[test]
    fn test_cranelift_real_compile_comparison() {
        let mut backend = CraneliftBackend::host();
        let mir = make_comparison_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Comparison should use real codegen"
        );
    }

    #[test]
    fn test_cranelift_real_compile_with_params() {
        let mut backend = CraneliftBackend::host();
        let mir = make_params_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Param function should use real codegen"
        );
    }

    #[test]
    fn test_cranelift_resource_function_uses_real_codegen() {
        let mut backend = CraneliftBackend::host();
        let mir = make_resource_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert!(
            module.functions[0].is_real_codegen,
            "Resource function should now use real codegen"
        );
    }

    // --- New tests for expanded Cranelift backend ---

    fn make_call_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let func_const = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Unit),
            kind: ConstantKind::Function(SmolStr::new("callee")),
        });

        let mut basic_blocks_callee: Arena<BasicBlock> = Arena::new();
        let entry_callee = basic_blocks_callee.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Nop,
            }],
            terminator: Terminator::Return(None),
        });
        let callee = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("callee"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks: basic_blocks_callee,
            entry_block: entry_callee,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        let mut basic_blocks_caller: Arena<BasicBlock> = Arena::new();
        let entry_caller = basic_blocks_caller.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Call {
                    target: None,
                    func: Value::Constant(func_const),
                    args: vec![],
                    resource_budget: None,
                },
            }],
            terminator: Terminator::Return(None),
        });
        let caller = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("caller"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks: basic_blocks_caller,
            entry_block: entry_caller,
            resource_constraints: vec![],
            is_adaptive: false,
        };

        MirFile {
            functions: vec![callee, caller],
            constants,
        }
    }

    #[test]
    fn test_cranelift_call_instruction() {
        let mut backend = CraneliftBackend::host();
        let mir = make_call_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 2);
        // Both callee and caller should use real codegen.
        assert!(
            module.functions[0].is_real_codegen,
            "callee should use real codegen"
        );
        assert!(
            module.functions[1].is_real_codegen,
            "caller with Call should use real codegen"
        );
    }

    fn make_store_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let ptr_const = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(0x1000),
        });
        let val_const = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(42),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Store {
                    ptr: Value::Constant(ptr_const),
                    value: Value::Constant(val_const),
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("store_fn"),
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

    #[test]
    fn test_cranelift_store_instruction() {
        let mut backend = CraneliftBackend::host();
        let mir = make_store_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Store should use real codegen"
        );
    }

    #[test]
    fn test_cranelift_resource_tracking() {
        // This test verifies that ResourceTrack now compiles to real native code
        // instead of falling back to estimation.
        let mut backend = CraneliftBackend::host();
        let mir = make_resource_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert!(module.functions[0].has_resource_tracking);
        assert!(
            module.functions[0].is_real_codegen,
            "ResourceTrack should now use real codegen"
        );
        assert!(module.functions[0].code_size > 0);
    }

    fn make_shadow_price_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ShadowPriceHook {
                    resource: SmolStr::new("memory"),
                    dimension: Dimension::memory(),
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("shadow_fn"),
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
    fn test_cranelift_shadow_price_hook() {
        let mut backend = CraneliftBackend::host();
        let mir = make_shadow_price_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "ShadowPriceHook should use real codegen"
        );
    }

    fn make_goto_mir() -> MirFile {
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();

        // Create exit block first so we have its BlockId.
        let exit_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("exit"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Nop,
            }],
            terminator: Terminator::Goto(exit_block),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("goto_fn"),
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
    fn test_cranelift_goto_terminator() {
        let mut backend = CraneliftBackend::host();
        let mir = make_goto_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Goto terminator should use real codegen"
        );
    }

    fn make_branch_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let cond_const = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I32),
            kind: ConstantKind::Int(1),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();

        let then_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("then"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let else_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("else"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Branch {
                condition: Value::Constant(cond_const),
                then_block,
                else_block,
            },
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("branch_fn"),
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

    #[test]
    fn test_cranelift_branch_terminator() {
        let mut backend = CraneliftBackend::host();
        let mir = make_branch_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Branch terminator should use real codegen"
        );
    }

    fn make_switch_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let switch_val = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::I64),
            kind: ConstantKind::Int(2),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();

        let case0_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case0"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let case1_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("case1"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let default_block = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("default"),
            instructions: vec![],
            terminator: Terminator::Return(None),
        });

        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![],
            terminator: Terminator::Switch {
                value: Value::Constant(switch_val),
                targets: vec![(0, case0_block), (1, case1_block)],
                default: default_block,
            },
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("switch_fn"),
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

    #[test]
    fn test_cranelift_switch_terminator() {
        let mut backend = CraneliftBackend::host();
        let mir = make_switch_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "Switch terminator should use real codegen"
        );
    }

    fn make_string_constant_mir() -> MirFile {
        let mut constants: Arena<Constant> = Arena::new();
        let str_const = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::String),
            kind: ConstantKind::String(SmolStr::new("hello world")),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Constant(str_const),
                },
            }],
            terminator: Terminator::Return(Some(Value::Local(0))),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("str_fn"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::I64),
            locals: vec![Local {
                id: 0,
                name: SmolStr::new("s"),
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

    #[test]
    fn test_cranelift_string_constant() {
        let mut backend = CraneliftBackend::host();
        let mir = make_string_constant_mir();
        let module = backend.generate(&mir).unwrap_ok();

        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].is_real_codegen,
            "String constant (placeholder) should use real codegen"
        );
    }

    #[test]
    fn test_cranelift_all_real_codegen() {
        // MIR with mixed constructs: all functions should compile with real codegen.
        let mut backend = CraneliftBackend::host();

        // Use the resource MIR (has ResourceTrack).
        let mir = make_resource_mir();
        let module = backend.generate(&mir).unwrap_ok();
        for f in &module.functions {
            assert!(
                f.is_real_codegen,
                "Function '{}' should use real codegen",
                f.name
            );
        }

        // Use the call MIR (has Call).
        let mir2 = make_call_mir();
        let module2 = backend.generate(&mir2).unwrap_ok();
        for f in &module2.functions {
            assert!(
                f.is_real_codegen,
                "Function '{}' should use real codegen",
                f.name
            );
        }

        // Use the store MIR (has Store).
        let mir3 = make_store_mir();
        let module3 = backend.generate(&mir3).unwrap_ok();
        for f in &module3.functions {
            assert!(
                f.is_real_codegen,
                "Function '{}' should use real codegen",
                f.name
            );
        }
    }
}
