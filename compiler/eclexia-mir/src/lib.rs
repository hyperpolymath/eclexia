// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Mid-level Intermediate Representation (MIR) for Eclexia.
//!
//! The MIR is a control-flow graph representation used for:
//! - Optimization passes (dead code elimination, constant folding, etc.)
//! - Resource constraint lowering and validation
//! - Shadow price hook insertion for runtime scheduling
//! - Preparation for code generation
//!
//! Key characteristics:
//! - Explicit control flow with basic blocks
//! - Simplified instruction set
//! - Resource tracking as explicit operations
//! - Ready for optimization and analysis

mod lower;
mod optimize;

pub use lower::{lower_hir_file, LoweringContext};
pub use optimize::{optimize, optimize_resource_tracking, insert_shadow_price_hooks, OptimizationLevel};

use eclexia_ast::dimension::Dimension;
use eclexia_ast::span::Span;
use eclexia_ast::types::{Ty, PrimitiveTy};
use la_arena::{Arena, Idx};
use smol_str::SmolStr;
use rustc_hash::FxHashMap;

/// A MIR file containing all functions
#[derive(Debug, Clone)]
pub struct MirFile {
    /// All functions in the file
    pub functions: Vec<Function>,
    /// Constant pool
    pub constants: Arena<Constant>,
}

impl MirFile {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            constants: Arena::new(),
        }
    }
}

impl Default for MirFile {
    fn default() -> Self {
        Self::new()
    }
}

/// Index types
pub type BlockId = Idx<BasicBlock>;
pub type InstructionId = Idx<Instruction>;
pub type ConstantId = Idx<Constant>;
pub type LocalId = u32;

/// A function in MIR form
#[derive(Debug, Clone)]
pub struct Function {
    pub span: Span,
    pub name: SmolStr,
    pub params: Vec<Local>,
    pub return_ty: Ty,
    pub locals: Vec<Local>,
    pub basic_blocks: Arena<BasicBlock>,
    pub entry_block: BlockId,
    /// Resource constraints for this function
    pub resource_constraints: Vec<ResourceConstraint>,
    /// Whether this is an adaptive function
    pub is_adaptive: bool,
}

/// An adaptive function with multiple solution branches
#[derive(Debug, Clone)]
pub struct AdaptiveFunction {
    pub span: Span,
    pub name: SmolStr,
    pub params: Vec<Local>,
    pub return_ty: Ty,
    pub solutions: Vec<Solution>,
    pub resource_constraints: Vec<ResourceConstraint>,
    pub optimization_objective: Option<Objective>,
}

/// A solution branch in an adaptive function
#[derive(Debug, Clone)]
pub struct Solution {
    pub name: SmolStr,
    pub condition: Option<Value>,
    pub function: Function,
    pub resource_costs: Vec<ResourceCost>,
}

/// Resource cost annotation for a solution
#[derive(Debug, Clone)]
pub struct ResourceCost {
    pub resource: SmolStr,
    pub dimension: Dimension,
    pub amount: f64,
}

/// Optimization objective
#[derive(Debug, Clone)]
pub struct Objective {
    pub direction: OptimizeDirection,
    pub target: SmolStr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizeDirection {
    Minimize,
    Maximize,
}

/// Resource constraint
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    pub resource: SmolStr,
    pub dimension: Dimension,
    pub op: ConstraintOp,
    pub bound: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// A basic block in the control flow graph
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub label: SmolStr,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

/// A local variable
#[derive(Debug, Clone)]
pub struct Local {
    pub id: LocalId,
    pub name: SmolStr,
    pub ty: Ty,
    pub mutable: bool,
}

/// A MIR instruction
#[derive(Debug, Clone)]
pub struct Instruction {
    pub span: Span,
    pub kind: InstructionKind,
}

#[derive(Debug, Clone)]
pub enum InstructionKind {
    /// Assign: local = value
    Assign {
        target: LocalId,
        value: Value,
    },

    /// Store to memory: *ptr = value
    Store {
        ptr: Value,
        value: Value,
    },

    /// Function call with resource tracking
    Call {
        target: Option<LocalId>,
        func: Value,
        args: Vec<Value>,
        /// Resource budget for this call
        resource_budget: Option<ResourceBudget>,
    },

    /// Track resource consumption
    ResourceTrack {
        resource: SmolStr,
        dimension: Dimension,
        amount: Value,
    },

    /// Shadow price hook for adaptive selection
    ShadowPriceHook {
        resource: SmolStr,
        dimension: Dimension,
    },

    /// No operation (for optimization targets)
    Nop,
}

/// Resource budget for a call
#[derive(Debug, Clone)]
pub struct ResourceBudget {
    pub energy: Option<f64>,
    pub time: Option<f64>,
    pub memory: Option<f64>,
    pub carbon: Option<f64>,
}

/// Block terminator (control flow)
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Return from function
    Return(Option<Value>),

    /// Unconditional jump
    Goto(BlockId),

    /// Conditional branch
    Branch {
        condition: Value,
        then_block: BlockId,
        else_block: BlockId,
    },

    /// Multi-way switch
    Switch {
        value: Value,
        targets: Vec<(i64, BlockId)>,
        default: BlockId,
    },

    /// Unreachable code
    Unreachable,
}

/// A value in MIR
#[derive(Debug, Clone)]
pub enum Value {
    /// Local variable reference
    Local(LocalId),

    /// Constant reference
    Constant(ConstantId),

    /// Binary operation
    Binary {
        op: BinaryOp,
        lhs: Box<Value>,
        rhs: Box<Value>,
    },

    /// Unary operation
    Unary {
        op: UnaryOp,
        operand: Box<Value>,
    },

    /// Load from memory
    Load {
        ptr: Box<Value>,
    },

    /// Field access
    Field {
        base: Box<Value>,
        field: SmolStr,
    },

    /// Index access
    Index {
        base: Box<Value>,
        index: Box<Value>,
    },

    /// Type cast
    Cast {
        value: Box<Value>,
        target_ty: Ty,
    },
}

/// A constant value
#[derive(Debug, Clone)]
pub struct Constant {
    pub ty: Ty,
    pub kind: ConstantKind,
}

#[derive(Debug, Clone)]
pub enum ConstantKind {
    Int(i64),
    Float(f64),
    String(SmolStr),
    Char(char),
    Bool(bool),
    Unit,
    /// Resource literal with dimension
    Resource {
        value: f64,
        dimension: Dimension,
        unit: Option<SmolStr>,
    },
    /// Function reference
    Function(SmolStr),
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

impl From<eclexia_hir::BinaryOp> for BinaryOp {
    fn from(op: eclexia_hir::BinaryOp) -> Self {
        match op {
            eclexia_hir::BinaryOp::Add => BinaryOp::Add,
            eclexia_hir::BinaryOp::Sub => BinaryOp::Sub,
            eclexia_hir::BinaryOp::Mul => BinaryOp::Mul,
            eclexia_hir::BinaryOp::Div => BinaryOp::Div,
            eclexia_hir::BinaryOp::Rem => BinaryOp::Rem,
            eclexia_hir::BinaryOp::Pow => BinaryOp::Mul, // Simplified
            eclexia_hir::BinaryOp::Eq => BinaryOp::Eq,
            eclexia_hir::BinaryOp::Ne => BinaryOp::Ne,
            eclexia_hir::BinaryOp::Lt => BinaryOp::Lt,
            eclexia_hir::BinaryOp::Le => BinaryOp::Le,
            eclexia_hir::BinaryOp::Gt => BinaryOp::Gt,
            eclexia_hir::BinaryOp::Ge => BinaryOp::Ge,
            eclexia_hir::BinaryOp::And => BinaryOp::And,
            eclexia_hir::BinaryOp::Or => BinaryOp::Or,
            eclexia_hir::BinaryOp::BitAnd => BinaryOp::BitAnd,
            eclexia_hir::BinaryOp::BitOr => BinaryOp::BitOr,
            eclexia_hir::BinaryOp::BitXor => BinaryOp::BitXor,
            eclexia_hir::BinaryOp::Shl => BinaryOp::Shl,
            eclexia_hir::BinaryOp::Shr => BinaryOp::Shr,
        }
    }
}

impl From<eclexia_hir::UnaryOp> for UnaryOp {
    fn from(op: eclexia_hir::UnaryOp) -> Self {
        match op {
            eclexia_hir::UnaryOp::Neg => UnaryOp::Neg,
            eclexia_hir::UnaryOp::Not => UnaryOp::Not,
            eclexia_hir::UnaryOp::BitNot => UnaryOp::BitNot,
        }
    }
}
