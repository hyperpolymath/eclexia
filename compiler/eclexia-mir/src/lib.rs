// SPDX-License-Identifier: PMPL-1.0-or-later
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
pub use optimize::{
    insert_shadow_price_hooks, optimize, optimize_resource_tracking, OptimizationLevel,
};

use eclexia_ast::dimension::Dimension;
use eclexia_ast::span::Span;
use eclexia_ast::types::{PrimitiveTy, Ty};
use la_arena::{Arena, Idx};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

/// A MIR file containing all functions
#[derive(Debug, Clone)]
pub struct MirFile {
    /// All functions in the file
    pub functions: Vec<Function>,
    /// Constant pool
    pub constants: Arena<Constant>,
}

impl MirFile {
    /// Create a new empty MIR file
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
    /// Source span
    pub span: Span,
    /// Function name
    pub name: SmolStr,
    /// Function parameters
    pub params: Vec<Local>,
    /// Return type
    pub return_ty: Ty,
    /// Local variable declarations
    pub locals: Vec<Local>,
    /// Arena of basic blocks forming the control flow graph
    pub basic_blocks: Arena<BasicBlock>,
    /// Entry point block
    pub entry_block: BlockId,
    /// Resource constraints for this function
    pub resource_constraints: Vec<ResourceConstraint>,
    /// Whether this is an adaptive function
    pub is_adaptive: bool,
}

/// An adaptive function with multiple solution branches
#[derive(Debug, Clone)]
pub struct AdaptiveFunction {
    /// Source span
    pub span: Span,
    /// Function name
    pub name: SmolStr,
    /// Function parameters
    pub params: Vec<Local>,
    /// Return type
    pub return_ty: Ty,
    /// Solution branches to choose from at runtime
    pub solutions: Vec<Solution>,
    /// Resource constraints
    pub resource_constraints: Vec<ResourceConstraint>,
    /// Optional optimization objective
    pub optimization_objective: Option<Objective>,
}

/// A solution branch in an adaptive function
#[derive(Debug, Clone)]
pub struct Solution {
    /// Solution name
    pub name: SmolStr,
    /// Optional guard condition
    pub condition: Option<Value>,
    /// Lowered function for this solution
    pub function: Function,
    /// Estimated resource costs
    pub resource_costs: Vec<ResourceCost>,
}

/// Resource cost annotation for a solution
#[derive(Debug, Clone)]
pub struct ResourceCost {
    /// Resource name
    pub resource: SmolStr,
    /// Physical dimension of the resource
    pub dimension: Dimension,
    /// Cost amount
    pub amount: f64,
}

/// Optimization objective
#[derive(Debug, Clone)]
pub struct Objective {
    /// Minimize or maximize
    pub direction: OptimizeDirection,
    /// Target metric name
    pub target: SmolStr,
}

/// Direction for optimization objectives
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizeDirection {
    /// Minimize the target metric
    Minimize,
    /// Maximize the target metric
    Maximize,
}

/// Resource constraint
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    /// Resource name (e.g., "energy", "time")
    pub resource: SmolStr,
    /// Physical dimension of the resource
    pub dimension: Dimension,
    /// Comparison operator
    pub op: ConstraintOp,
    /// Bound value
    pub bound: f64,
}

/// Comparison operator for resource constraints
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintOp {
    /// Less than
    Lt,
    /// Less than or equal
    Le,
    /// Greater than
    Gt,
    /// Greater than or equal
    Ge,
    /// Equal
    Eq,
    /// Not equal
    Ne,
}

/// A basic block in the control flow graph
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Block label for debugging
    pub label: SmolStr,
    /// Instructions in this block
    pub instructions: Vec<Instruction>,
    /// Control flow terminator
    pub terminator: Terminator,
}

/// A local variable
#[derive(Debug, Clone)]
pub struct Local {
    /// Unique local identifier
    pub id: LocalId,
    /// Variable name
    pub name: SmolStr,
    /// Variable type
    pub ty: Ty,
    /// Whether this variable is mutable
    pub mutable: bool,
}

/// A MIR instruction
#[derive(Debug, Clone)]
pub struct Instruction {
    /// Source span
    pub span: Span,
    /// Instruction kind
    pub kind: InstructionKind,
}

#[derive(Debug, Clone)]
pub enum InstructionKind {
    /// Assign: local = value
    Assign { target: LocalId, value: Value },

    /// Store to memory: *ptr = value
    Store { ptr: Value, value: Value },

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
    /// Energy budget in joules
    pub energy: Option<f64>,
    /// Time budget in seconds
    pub time: Option<f64>,
    /// Memory budget in bytes
    pub memory: Option<f64>,
    /// Carbon budget in grams CO2
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
    Unary { op: UnaryOp, operand: Box<Value> },

    /// Load from memory
    Load { ptr: Box<Value> },

    /// Field access
    Field { base: Box<Value>, field: SmolStr },

    /// Index access
    Index { base: Box<Value>, index: Box<Value> },

    /// Type cast
    Cast { value: Box<Value>, target_ty: Ty },
}

/// A constant value
#[derive(Debug, Clone)]
pub struct Constant {
    /// Type of the constant
    pub ty: Ty,
    /// Constant value kind
    pub kind: ConstantKind,
}

/// Kind of constant value
#[derive(Debug, Clone)]
pub enum ConstantKind {
    /// Integer constant
    Int(i64),
    /// Floating-point constant
    Float(f64),
    /// String constant
    String(SmolStr),
    /// Character constant
    Char(char),
    /// Boolean constant
    Bool(bool),
    /// Unit constant `()`
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
    /// Addition (`+`)
    Add,
    /// Subtraction (`-`)
    Sub,
    /// Multiplication (`*`)
    Mul,
    /// Division (`/`)
    Div,
    /// Remainder (`%`)
    Rem,
    /// Exponentiation (`**`)
    Pow,

    /// Equality comparison (`==`)
    Eq,
    /// Inequality comparison (`!=`)
    Ne,
    /// Less than (`<`)
    Lt,
    /// Less than or equal (`<=`)
    Le,
    /// Greater than (`>`)
    Gt,
    /// Greater than or equal (`>=`)
    Ge,

    /// Logical AND (`&&`)
    And,
    /// Logical OR (`||`)
    Or,

    /// Bitwise AND (`&`)
    BitAnd,
    /// Bitwise OR (`|`)
    BitOr,
    /// Bitwise XOR (`^`)
    BitXor,
    /// Left shift (`<<`)
    Shl,
    /// Right shift (`>>`)
    Shr,

    /// Exclusive range (`..`)
    Range,
    /// Inclusive range (`..=`)
    RangeInclusive,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Arithmetic negation (`-`)
    Neg,
    /// Logical NOT (`!`)
    Not,
    /// Bitwise NOT (`~`)
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
            eclexia_hir::BinaryOp::Pow => BinaryOp::Pow,
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
            eclexia_hir::BinaryOp::Range => BinaryOp::Range,
            eclexia_hir::BinaryOp::RangeInclusive => BinaryOp::RangeInclusive,
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
