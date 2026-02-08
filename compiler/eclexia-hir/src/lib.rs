// SPDX-License-Identifier: AGPL-3.0-or-later
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
use eclexia_ast::types::{Ty, PrimitiveTy};
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
    TraitDecl {
        span: Span,
        name: SmolStr,
    },
    /// Impl block (placeholder for future use)
    ImplBlock {
        span: Span,
        self_ty_name: SmolStr,
    },
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
}

/// A function definition
#[derive(Debug, Clone)]
pub struct Function {
    pub span: Span,
    pub name: SmolStr,
    pub params: Vec<Param>,
    pub return_ty: Ty,
    pub constraints: Vec<ResourceConstraint>,
    pub body: Body,
}

/// An adaptive function with multiple solution implementations
#[derive(Debug, Clone)]
pub struct AdaptiveFunction {
    pub span: Span,
    pub name: SmolStr,
    pub params: Vec<Param>,
    pub return_ty: Ty,
    pub constraints: Vec<ResourceConstraint>,
    pub optimize: Vec<Objective>,
    pub solutions: Vec<Solution>,
}

/// A solution branch in an adaptive function
#[derive(Debug, Clone)]
pub struct Solution {
    pub span: Span,
    pub name: SmolStr,
    pub when_clause: Option<ExprId>,
    pub provides: Vec<ResourceProvision>,
    pub body: Body,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub span: Span,
    pub name: SmolStr,
    pub ty: Ty,
    pub local: LocalId,
}

/// Function body
#[derive(Debug, Clone)]
pub struct Body {
    pub stmts: Vec<StmtId>,
    pub expr: Option<ExprId>,
}

/// A local variable
#[derive(Debug, Clone)]
pub struct Local {
    pub span: Span,
    pub name: SmolStr,
    pub ty: Ty,
    pub mutable: bool,
}

/// Resource constraint on a function
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    pub span: Span,
    pub resource: SmolStr,
    pub dimension: Dimension,
    pub op: ConstraintOp,
    pub bound: f64,
    pub unit: Option<SmolStr>,
}

/// Resource provision in a solution
#[derive(Debug, Clone)]
pub struct ResourceProvision {
    pub span: Span,
    pub resource: SmolStr,
    pub dimension: Dimension,
    pub amount: f64,
    pub unit: Option<SmolStr>,
}

/// Optimization objective
#[derive(Debug, Clone)]
pub struct Objective {
    pub span: Span,
    pub direction: OptimizeDirection,
    pub target: SmolStr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizeDirection {
    Minimize,
    Maximize,
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

/// Type definition
#[derive(Debug, Clone)]
pub struct TypeDef {
    pub span: Span,
    pub name: SmolStr,
    pub kind: TypeDefKind,
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    Struct {
        fields: Vec<Field>,
    },
    Enum {
        variants: Vec<Variant>,
    },
    Alias {
        target: Ty,
    },
}

/// Struct field
#[derive(Debug, Clone)]
pub struct Field {
    pub span: Span,
    pub name: SmolStr,
    pub ty: Ty,
}

/// Enum variant
#[derive(Debug, Clone)]
pub struct Variant {
    pub span: Span,
    pub name: SmolStr,
    pub fields: Vec<Ty>,
}

/// Constant definition
#[derive(Debug, Clone)]
pub struct Const {
    pub span: Span,
    pub name: SmolStr,
    pub ty: Ty,
    pub value: ExprId,
}

/// A statement
#[derive(Debug, Clone)]
pub struct Stmt {
    pub span: Span,
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
    Assign {
        place: Place,
        value: ExprId,
    },
    /// Expression statement
    Expr(ExprId),
    /// Return from function
    Return(Option<ExprId>),
    /// Infinite loop
    InfiniteLoop {
        label: Option<SmolStr>,
        body: Body,
    },
    /// Break from loop
    Break {
        label: Option<SmolStr>,
        value: Option<ExprId>,
    },
    /// Continue loop
    Continue {
        label: Option<SmolStr>,
    },
}

/// A place (lvalue)
#[derive(Debug, Clone)]
pub enum Place {
    /// Local variable
    Local(LocalId),
    /// Field access
    Field {
        base: Box<Place>,
        field: SmolStr,
    },
    /// Index access
    Index {
        base: Box<Place>,
        index: ExprId,
    },
}

/// An expression
#[derive(Debug, Clone)]
pub struct Expr {
    pub span: Span,
    pub ty: Ty,
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
    Unary {
        op: UnaryOp,
        operand: ExprId,
    },

    /// Function call
    Call {
        func: ExprId,
        args: Vec<ExprId>,
    },

    /// If expression
    If {
        condition: ExprId,
        then_branch: Body,
        else_branch: Option<Body>,
    },

    /// While loop
    Loop {
        condition: ExprId,
        body: Body,
    },

    /// Block expression
    Block(Body),

    /// Tuple construction
    Tuple(Vec<ExprId>),

    /// Array construction
    Array(Vec<ExprId>),

    /// Field access
    Field {
        expr: ExprId,
        field: SmolStr,
    },

    /// Index access
    Index {
        expr: ExprId,
        index: ExprId,
    },

    /// Lambda function
    Lambda {
        params: Vec<Param>,
        body: Body,
    },

    /// Struct construction
    Struct {
        name: SmolStr,
        fields: Vec<(SmolStr, ExprId)>,
    },

    /// Type cast
    Cast {
        expr: ExprId,
        target_ty: Ty,
    },

    /// Assignment
    Assign {
        target: LocalId,
        value: ExprId,
    },

    /// Try operator (expr?)
    Try(ExprId),

    /// Borrow (&expr or &mut expr)
    Borrow {
        expr: ExprId,
        mutable: bool,
    },

    /// Dereference (*expr)
    Deref(ExprId),

    /// Array repeat [value; count]
    ArrayRepeat {
        value: ExprId,
        count: ExprId,
    },

    /// Infinite loop as expression
    InfiniteLoop {
        label: Option<SmolStr>,
        body: Body,
    },

    /// Return as expression
    ReturnExpr(Option<ExprId>),

    /// Break as expression
    BreakExpr {
        label: Option<SmolStr>,
        value: Option<ExprId>,
    },

    /// Continue as expression
    ContinueExpr {
        label: Option<SmolStr>,
    },
}

/// Literal value
#[derive(Debug, Clone)]
pub enum Literal {
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
    Pow,

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

    // Range
    Range,
    RangeInclusive,
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
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
