// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Abstract Syntax Tree definitions for the Eclexia programming language.
//!
//! This crate defines the core AST nodes that represent Eclexia programs
//! after parsing. The AST preserves source locations for error reporting
//! and includes all syntactic constructs including:
//!
//! - Resource types with dimensional analysis
//! - Adaptive blocks with solution alternatives
//! - Constraint annotations (@requires, @provides, @optimize)
//! - Standard expressions and statements

pub mod dimension;
pub mod span;
pub mod types;

use la_arena::{Arena, Idx};
use smol_str::SmolStr;
use span::Span;

/// Interned string type for identifiers
pub type Ident = SmolStr;

/// Index into an expression arena
pub type ExprId = Idx<Expr>;

/// Index into a statement arena
pub type StmtId = Idx<Stmt>;

/// Index into a type arena
pub type TypeId = Idx<Type>;

/// A complete Eclexia source file
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceFile {
    /// Module-level items (functions, types, imports)
    pub items: Vec<Item>,
    /// Expression arena for this file
    pub exprs: Arena<Expr>,
    /// Statement arena
    pub stmts: Arena<Stmt>,
    /// Type arena
    pub types: Arena<Type>,
}

impl SourceFile {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            exprs: Arena::new(),
            stmts: Arena::new(),
            types: Arena::new(),
        }
    }
}

impl Default for SourceFile {
    fn default() -> Self {
        Self::new()
    }
}

/// An attribute attached to an item (#[attr] or #[attr(args)])
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Attribute {
    pub span: Span,
    pub name: Ident,
    pub args: Vec<Ident>,
}

/// Top-level item in a source file
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Item {
    /// Function definition
    Function(Function),
    /// Adaptive function definition
    AdaptiveFunction(AdaptiveFunction),
    /// Type definition
    TypeDef(TypeDef),
    /// Import statement
    Import(Import),
    /// Constant definition
    Const(ConstDef),
}

/// A regular function definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Function {
    pub span: Span,
    pub name: Ident,
    pub type_params: Vec<Ident>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeId>,
    pub constraints: Vec<Constraint>,
    pub attributes: Vec<Attribute>,
    pub body: Block,
}

/// An adaptive function with multiple solution alternatives
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AdaptiveFunction {
    pub span: Span,
    pub name: Ident,
    pub type_params: Vec<Ident>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeId>,
    pub constraints: Vec<Constraint>,
    pub attributes: Vec<Attribute>,
    pub optimize: Vec<Objective>,
    pub solutions: Vec<Solution>,
}

/// A solution alternative within an adaptive function
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Solution {
    pub span: Span,
    pub name: Ident,
    pub when_clause: Option<ExprId>,
    pub provides: Vec<ResourceProvision>,
    pub body: Block,
}

/// Resource provision declaration (@provides)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ResourceProvision {
    pub span: Span,
    pub resource: Ident,
    pub amount: ResourceAmount,
}

/// A resource amount with optional unit
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ResourceAmount {
    pub value: f64,
    pub unit: Option<Ident>,
}

/// Function parameter
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Param {
    pub span: Span,
    pub name: Ident,
    pub ty: Option<TypeId>,
}

/// Constraint annotation (@requires)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Constraint {
    pub span: Span,
    pub kind: ConstraintKind,
}

/// Kind of constraint
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstraintKind {
    /// Resource budget: energy < 100J
    Resource {
        resource: Ident,
        op: CompareOp,
        amount: ResourceAmount,
    },
    /// Custom predicate
    Predicate(ExprId),
}

/// Optimization objective
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Objective {
    pub span: Span,
    pub direction: OptimizeDirection,
    pub target: Ident,
}

/// Optimization direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OptimizeDirection {
    Minimize,
    Maximize,
}

/// Comparison operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CompareOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// Type definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeDef {
    pub span: Span,
    pub name: Ident,
    pub params: Vec<Ident>,
    pub kind: TypeDefKind,
}

/// Kind of type definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeDefKind {
    /// Type alias
    Alias(TypeId),
    /// Struct/record type
    Struct(Vec<Field>),
    /// Enum/variant type
    Enum(Vec<Variant>),
}

/// Struct field
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Field {
    pub span: Span,
    pub name: Ident,
    pub ty: TypeId,
}

/// Enum variant
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Variant {
    pub span: Span,
    pub name: Ident,
    pub fields: Option<Vec<TypeId>>,
}

/// Import statement
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Import {
    pub span: Span,
    pub path: Vec<Ident>,
    pub alias: Option<Ident>,
}

/// Constant definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConstDef {
    pub span: Span,
    pub name: Ident,
    pub ty: Option<TypeId>,
    pub value: ExprId,
}

/// A block of statements
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Block {
    pub span: Span,
    pub stmts: Vec<StmtId>,
    /// Optional trailing expression (block value)
    pub expr: Option<ExprId>,
}

/// Statement
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

/// Statement kind
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StmtKind {
    /// Let binding
    Let {
        name: Ident,
        ty: Option<TypeId>,
        value: ExprId,
    },
    /// Expression statement
    Expr(ExprId),
    /// Return statement
    Return(Option<ExprId>),
    /// While loop
    While { condition: ExprId, body: Block },
    /// For loop
    For {
        name: Ident,
        iter: ExprId,
        body: Block,
    },
}

/// Expression
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

/// Expression kind
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExprKind {
    /// Literal value
    Literal(Literal),
    /// Variable reference
    Var(Ident),
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
    /// Method call
    MethodCall {
        receiver: ExprId,
        method: Ident,
        args: Vec<ExprId>,
    },
    /// Field access
    Field { expr: ExprId, field: Ident },
    /// Index access
    Index { expr: ExprId, index: ExprId },
    /// If expression
    If {
        condition: ExprId,
        then_branch: Block,
        else_branch: Option<Block>,
    },
    /// Match expression
    Match {
        scrutinee: ExprId,
        arms: Vec<MatchArm>,
    },
    /// Block expression
    Block(Block),
    /// Lambda/closure
    Lambda { params: Vec<Param>, body: ExprId },
    /// Tuple construction
    Tuple(Vec<ExprId>),
    /// Array literal
    Array(Vec<ExprId>),
    /// Struct literal
    Struct {
        name: Ident,
        fields: Vec<(Ident, ExprId)>,
    },
    /// Resource literal (e.g., 100J, 5ms, 10gCO2e)
    Resource(ResourceAmount),
    /// Error placeholder for recovery
    Error,
}

/// Match arm
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MatchArm {
    pub span: Span,
    pub pattern: Pattern,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

/// Pattern for matching
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Pattern {
    /// Wildcard pattern (_)
    Wildcard,
    /// Variable binding
    Var(Ident),
    /// Literal pattern
    Literal(Literal),
    /// Tuple pattern
    Tuple(Vec<Pattern>),
    /// Constructor pattern
    Constructor { name: Ident, fields: Vec<Pattern> },
}

/// Literal value
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Literal {
    /// Integer literal
    Int(i64),
    /// Float literal
    Float(f64),
    /// String literal
    String(SmolStr),
    /// Character literal
    Char(char),
    /// Boolean literal
    Bool(bool),
    /// Unit literal ()
    Unit,
}

/// Binary operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
}

/// Unary operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

/// Type expression
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

/// Type expression kind
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeKind {
    /// Named type (possibly generic)
    Named { name: Ident, args: Vec<TypeId> },
    /// Function type
    Function { params: Vec<TypeId>, ret: TypeId },
    /// Tuple type
    Tuple(Vec<TypeId>),
    /// Array type with optional size
    Array { elem: TypeId, size: Option<usize> },
    /// Resource type with dimension
    Resource { base: Ident, dimension: dimension::Dimension },
    /// Infer type (_)
    Infer,
    /// Error placeholder
    Error,
}
