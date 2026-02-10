// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! High-level Intermediate Representation (HIR) for Eclexia.
//!
//! The HIR is a desugared, type-annotated representation of the AST.
//! It preserves resource annotations and adaptive block structure
//! while simplifying the syntax for easier optimization.
//!
//! Key transformations from AST to HIR:
//! - All expressions have explicit type annotations
//! - Complex control flow desugared (for → while, match → if chains)
//! - Resource constraints preserved on functions
//! - Adaptive blocks maintained as first-class constructs
//! - Method calls desugared to function calls
//! - Implicit conversions made explicit

mod lower;

pub use lower::{lower_source_file, LoweringContext};

use eclexia_ast::dimension::Dimension;
use eclexia_ast::span::Span;
use eclexia_ast::types::{PrimitiveTy, Ty};
use la_arena::{Arena, Idx};
use smol_str::SmolStr;

/// A HIR source file
#[derive(Debug, Clone)]
pub struct HirFile {
    /// Top-level items
    pub items: Vec<Item>,
    /// Expression arena
    pub exprs: Arena<Expr>,
    /// Statement arena
    pub stmts: Arena<Stmt>,
    /// Local variable definitions
    pub locals: Arena<Local>,
}

impl HirFile {
    /// Create a new empty HIR file
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            exprs: Arena::new(),
            stmts: Arena::new(),
            locals: Arena::new(),
        }
    }
}

impl Default for HirFile {
    fn default() -> Self {
        Self::new()
    }
}

/// Index types
pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type LocalId = Idx<Local>;

/// A top-level item
#[derive(Debug, Clone)]
pub enum Item {
    /// Regular function
    Function(Function),
    /// Adaptive function with multiple solutions
    AdaptiveFunction(AdaptiveFunction),
    /// Type definition
    TypeDef(TypeDef),
    /// Constant definition
    Const(Const),
    /// Trait declaration (placeholder for future use)
    TraitDecl { span: Span, name: SmolStr },
    /// Impl block (placeholder for future use)
    ImplBlock { span: Span, self_ty_name: SmolStr },
    /// Module declaration
    Module {
        span: Span,
        name: SmolStr,
        items: Vec<Item>,
    },
    /// Static variable
    Static {
        span: Span,
        name: SmolStr,
        ty: Ty,
        value: ExprId,
        mutable: bool,
    },
    /// Error placeholder from resilient parsing
    Error(Span),
}

/// A function definition
#[derive(Debug, Clone)]
pub struct Function {
    /// Source span of the function
    pub span: Span,
    /// Function name
    pub name: SmolStr,
    /// Function parameters
    pub params: Vec<Param>,
    /// Return type
    pub return_ty: Ty,
    /// Resource constraints on this function
    pub constraints: Vec<ResourceConstraint>,
    /// Function body
    pub body: Body,
}

/// An adaptive function with multiple solution implementations
#[derive(Debug, Clone)]
pub struct AdaptiveFunction {
    /// Source span
    pub span: Span,
    /// Function name
    pub name: SmolStr,
    /// Function parameters
    pub params: Vec<Param>,
    /// Return type
    pub return_ty: Ty,
    /// Resource constraints on this function
    pub constraints: Vec<ResourceConstraint>,
    /// Optimization objectives to satisfy
    pub optimize: Vec<Objective>,
    /// Solution branches
    pub solutions: Vec<Solution>,
}

/// A solution branch in an adaptive function
#[derive(Debug, Clone)]
pub struct Solution {
    /// Source span
    pub span: Span,
    /// Solution name
    pub name: SmolStr,
    /// Optional guard condition for this solution
    pub when_clause: Option<ExprId>,
    /// Resources provided by this solution
    pub provides: Vec<ResourceProvision>,
    /// Solution body
    pub body: Body,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Param {
    /// Source span
    pub span: Span,
    /// Parameter name
    pub name: SmolStr,
    /// Parameter type
    pub ty: Ty,
    /// Local variable binding for this parameter
    pub local: LocalId,
}

/// Function body
#[derive(Debug, Clone)]
pub struct Body {
    /// Statements in the body
    pub stmts: Vec<StmtId>,
    /// Optional trailing expression (implicit return value)
    pub expr: Option<ExprId>,
}

/// A local variable
#[derive(Debug, Clone)]
pub struct Local {
    /// Source span
    pub span: Span,
    /// Variable name
    pub name: SmolStr,
    /// Variable type
    pub ty: Ty,
    /// Whether this variable is mutable
    pub mutable: bool,
}

/// Resource constraint on a function
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    /// Source span
    pub span: Span,
    /// Resource name (e.g., "energy", "time")
    pub resource: SmolStr,
    /// Physical dimension of the resource
    pub dimension: Dimension,
    /// Comparison operator
    pub op: ConstraintOp,
    /// Upper or lower bound value
    pub bound: f64,
    /// Optional unit label
    pub unit: Option<SmolStr>,
}

/// Resource provision in a solution
#[derive(Debug, Clone)]
pub struct ResourceProvision {
    /// Source span
    pub span: Span,
    /// Resource name
    pub resource: SmolStr,
    /// Physical dimension of the resource
    pub dimension: Dimension,
    /// Amount of resource provided
    pub amount: f64,
    /// Optional unit label
    pub unit: Option<SmolStr>,
}

/// Optimization objective
#[derive(Debug, Clone)]
pub struct Objective {
    /// Source span
    pub span: Span,
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

/// Type definition
#[derive(Debug, Clone)]
pub struct TypeDef {
    /// Source span
    pub span: Span,
    /// Type name
    pub name: SmolStr,
    /// Kind of type definition (struct, enum, or alias)
    pub kind: TypeDefKind,
}

/// The kind of a type definition
#[derive(Debug, Clone)]
pub enum TypeDefKind {
    /// Struct with named fields
    Struct { fields: Vec<Field> },
    /// Enum with variant constructors
    Enum { variants: Vec<Variant> },
    /// Type alias pointing to another type
    Alias { target: Ty },
}

/// Struct field
#[derive(Debug, Clone)]
pub struct Field {
    /// Source span
    pub span: Span,
    /// Field name
    pub name: SmolStr,
    /// Field type
    pub ty: Ty,
}

/// Enum variant
#[derive(Debug, Clone)]
pub struct Variant {
    /// Source span
    pub span: Span,
    /// Variant name
    pub name: SmolStr,
    /// Positional field types
    pub fields: Vec<Ty>,
}

/// Constant definition
#[derive(Debug, Clone)]
pub struct Const {
    /// Source span
    pub span: Span,
    /// Constant name
    pub name: SmolStr,
    /// Constant type
    pub ty: Ty,
    /// Constant value expression
    pub value: ExprId,
}

/// A statement
#[derive(Debug, Clone)]
pub struct Stmt {
    /// Source span
    pub span: Span,
    /// Statement kind
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// Let binding
    Let {
        local: LocalId,
        init: Option<ExprId>,
    },
    /// Assignment
    Assign { place: Place, value: ExprId },
    /// Expression statement
    Expr(ExprId),
    /// Return from function
    Return(Option<ExprId>),
    /// Infinite loop
    InfiniteLoop { label: Option<SmolStr>, body: Body },
    /// Break from loop
    Break {
        label: Option<SmolStr>,
        value: Option<ExprId>,
    },
    /// Continue loop
    Continue { label: Option<SmolStr> },
    /// Error placeholder from resilient parsing
    Error,
}

/// A place (lvalue)
#[derive(Debug, Clone)]
pub enum Place {
    /// Local variable
    Local(LocalId),
    /// Field access
    Field { base: Box<Place>, field: SmolStr },
    /// Index access
    Index { base: Box<Place>, index: ExprId },
}

/// An expression
#[derive(Debug, Clone)]
pub struct Expr {
    /// Source span
    pub span: Span,
    /// Resolved type of this expression
    pub ty: Ty,
    /// Expression kind
    pub kind: ExprKind,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// Literal value
    Literal(Literal),

    /// Local variable reference
    Local(LocalId),

    /// Binary operation
    Binary {
        op: BinaryOp,
        lhs: ExprId,
        rhs: ExprId,
    },

    /// Unary operation
    Unary { op: UnaryOp, operand: ExprId },

    /// Function call
    Call { func: ExprId, args: Vec<ExprId> },

    /// If expression
    If {
        condition: ExprId,
        then_branch: Body,
        else_branch: Option<Body>,
    },

    /// While loop
    Loop { condition: ExprId, body: Body },

    /// Block expression
    Block(Body),

    /// Tuple construction
    Tuple(Vec<ExprId>),

    /// Array construction
    Array(Vec<ExprId>),

    /// Field access
    Field { expr: ExprId, field: SmolStr },

    /// Index access
    Index { expr: ExprId, index: ExprId },

    /// Lambda function
    Lambda { params: Vec<Param>, body: Body },

    /// Struct construction
    Struct {
        name: SmolStr,
        fields: Vec<(SmolStr, ExprId)>,
    },

    /// Type cast
    Cast { expr: ExprId, target_ty: Ty },

    /// Assignment
    Assign { target: LocalId, value: ExprId },

    /// Try operator (expr?)
    Try(ExprId),

    /// Borrow (&expr or &mut expr)
    Borrow { expr: ExprId, mutable: bool },

    /// Dereference (*expr)
    Deref(ExprId),

    /// Array repeat [value; count]
    ArrayRepeat { value: ExprId, count: ExprId },

    /// Infinite loop as expression
    InfiniteLoop { label: Option<SmolStr>, body: Body },

    /// Return as expression
    ReturnExpr(Option<ExprId>),

    /// Break as expression
    BreakExpr {
        label: Option<SmolStr>,
        value: Option<ExprId>,
    },

    /// Continue as expression
    ContinueExpr { label: Option<SmolStr> },
}

/// Literal value
#[derive(Debug, Clone)]
pub enum Literal {
    /// Integer literal
    Int(i64),
    /// Floating-point literal
    Float(f64),
    /// String literal
    String(SmolStr),
    /// Character literal
    Char(char),
    /// Boolean literal
    Bool(bool),
    /// Unit literal `()`
    Unit,
    /// Resource literal with dimension
    Resource {
        value: f64,
        dimension: Dimension,
        unit: Option<SmolStr>,
    },
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

impl From<eclexia_ast::BinaryOp> for BinaryOp {
    fn from(op: eclexia_ast::BinaryOp) -> Self {
        match op {
            eclexia_ast::BinaryOp::Add => BinaryOp::Add,
            eclexia_ast::BinaryOp::Sub => BinaryOp::Sub,
            eclexia_ast::BinaryOp::Mul => BinaryOp::Mul,
            eclexia_ast::BinaryOp::Div => BinaryOp::Div,
            eclexia_ast::BinaryOp::Rem => BinaryOp::Rem,
            eclexia_ast::BinaryOp::Pow => BinaryOp::Pow,
            eclexia_ast::BinaryOp::Eq => BinaryOp::Eq,
            eclexia_ast::BinaryOp::Ne => BinaryOp::Ne,
            eclexia_ast::BinaryOp::Lt => BinaryOp::Lt,
            eclexia_ast::BinaryOp::Le => BinaryOp::Le,
            eclexia_ast::BinaryOp::Gt => BinaryOp::Gt,
            eclexia_ast::BinaryOp::Ge => BinaryOp::Ge,
            eclexia_ast::BinaryOp::And => BinaryOp::And,
            eclexia_ast::BinaryOp::Or => BinaryOp::Or,
            eclexia_ast::BinaryOp::BitAnd => BinaryOp::BitAnd,
            eclexia_ast::BinaryOp::BitOr => BinaryOp::BitOr,
            eclexia_ast::BinaryOp::BitXor => BinaryOp::BitXor,
            eclexia_ast::BinaryOp::Shl => BinaryOp::Shl,
            eclexia_ast::BinaryOp::Shr => BinaryOp::Shr,
            eclexia_ast::BinaryOp::Range => BinaryOp::Range,
            eclexia_ast::BinaryOp::RangeInclusive => BinaryOp::RangeInclusive,
        }
    }
}

impl From<eclexia_ast::UnaryOp> for UnaryOp {
    fn from(op: eclexia_ast::UnaryOp) -> Self {
        match op {
            eclexia_ast::UnaryOp::Neg => UnaryOp::Neg,
            eclexia_ast::UnaryOp::Not => UnaryOp::Not,
            eclexia_ast::UnaryOp::BitNot => UnaryOp::BitNot,
        }
    }
}
