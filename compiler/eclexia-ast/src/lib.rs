// SPDX-License-Identifier: PMPL-1.0-or-later
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
//! - Traits, impl blocks, modules, effects
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
    /// Source location of the attribute
    pub span: Span,
    /// Name of the attribute (e.g., `inline`, `test`)
    pub name: Ident,
    /// Arguments passed to the attribute
    pub args: Vec<Ident>,
}

// === Visibility ===

/// Visibility modifier
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Visibility {
    /// No visibility modifier (private by default)
    Private,
    /// `pub`
    Public,
    /// `pub(crate)`
    PubCrate,
}

impl Default for Visibility {
    fn default() -> Self {
        Visibility::Private
    }
}

// === Path ===

/// A qualified path (e.g., `foo::bar::Baz`)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Path {
    /// Source location of the path
    pub span: Span,
    /// Segments of the qualified path (e.g., `["foo", "bar", "Baz"]`)
    pub segments: Vec<Ident>,
}

// === Type Parameters & Bounds ===

/// A type parameter with optional bounds (e.g., `T: Display + Debug`)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeParam {
    /// Source location of the type parameter
    pub span: Span,
    /// Name of the type parameter (e.g., `T`)
    pub name: Ident,
    /// Trait bounds on this parameter (e.g., `Display + Debug`)
    pub bounds: Vec<TraitBound>,
}

/// A trait bound on a type parameter
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TraitBound {
    /// Source location of the trait bound
    pub span: Span,
    /// Qualified path to the trait (e.g., `["std", "fmt", "Display"]`)
    pub path: Vec<Ident>,
    /// Type arguments applied to the trait (e.g., the `String` in `Into<String>`)
    pub type_args: Vec<TypeId>,
}

/// A where predicate (e.g., `where T: Display`)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct WherePredicate {
    /// Source location of the where predicate
    pub span: Span,
    /// The type being constrained
    pub ty: TypeId,
    /// Trait bounds required for the type
    pub bounds: Vec<TraitBound>,
}

// === Function Signature ===

/// A function signature (shared between trait items, impl items, and top-level)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionSig {
    /// Source location of the function signature
    pub span: Span,
    /// Name of the function
    pub name: Ident,
    /// Generic type parameters
    pub type_params: Vec<TypeParam>,
    /// Function parameters
    pub params: Vec<Param>,
    /// Return type (None for implicit unit return)
    pub return_type: Option<TypeId>,
    /// Where clause constraints
    pub where_clause: Vec<WherePredicate>,
}

// === Top-level Items ===

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
    /// Trait declaration
    TraitDecl(TraitDecl),
    /// Impl block
    ImplBlock(ImplBlock),
    /// Module declaration
    ModuleDecl(ModuleDecl),
    /// Effect declaration
    EffectDecl(EffectDecl),
    /// Static declaration
    StaticDecl(StaticDecl),
    /// Extern block
    ExternBlock(ExternBlock),
    /// Macro definition
    MacroDef(MacroDef),
    /// Error placeholder for resilient parsing
    Error(Span),
}

/// A regular function definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Function {
    /// Source location of the function definition
    pub span: Span,
    /// Visibility modifier (pub, pub(crate), or private)
    pub visibility: Visibility,
    /// Name of the function
    pub name: Ident,
    /// Generic type parameter names
    pub type_params: Vec<Ident>,
    /// Function parameters
    pub params: Vec<Param>,
    /// Return type annotation (None for implicit unit)
    pub return_type: Option<TypeId>,
    /// Resource constraints (@requires annotations)
    pub constraints: Vec<Constraint>,
    /// Attributes attached to the function
    pub attributes: Vec<Attribute>,
    /// Where clause constraints
    pub where_clause: Vec<WherePredicate>,
    /// Function body
    pub body: Block,
}

/// An adaptive function with multiple solution alternatives
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AdaptiveFunction {
    /// Source location of the adaptive function
    pub span: Span,
    /// Name of the adaptive function
    pub name: Ident,
    /// Generic type parameter names
    pub type_params: Vec<Ident>,
    /// Function parameters
    pub params: Vec<Param>,
    /// Return type annotation (None for implicit unit)
    pub return_type: Option<TypeId>,
    /// Resource constraints (@requires annotations)
    pub constraints: Vec<Constraint>,
    /// Attributes attached to the function
    pub attributes: Vec<Attribute>,
    /// Optimization objectives (@optimize annotations)
    pub optimize: Vec<Objective>,
    /// Solution alternatives the runtime can choose between
    pub solutions: Vec<Solution>,
}

/// A solution alternative within an adaptive function
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Solution {
    /// Source location of the solution alternative
    pub span: Span,
    /// Name identifying this solution alternative
    pub name: Ident,
    /// Optional guard condition for when this solution applies
    pub when_clause: Option<ExprId>,
    /// Resource provisions this solution declares (@provides)
    pub provides: Vec<ResourceProvision>,
    /// Implementation body of this solution
    pub body: Block,
}

/// Resource provision declaration (@provides)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ResourceProvision {
    /// Source location of the resource provision
    pub span: Span,
    /// Name of the resource being provided (e.g., `energy`, `time`)
    pub resource: Ident,
    /// Amount of the resource provided
    pub amount: ResourceAmount,
}

/// A resource amount with optional unit
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ResourceAmount {
    /// Numeric value of the resource amount
    pub value: f64,
    /// Optional unit suffix (e.g., `J`, `ms`, `gCO2e`)
    pub unit: Option<Ident>,
}

/// Function parameter
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Param {
    /// Source location of the parameter
    pub span: Span,
    /// Parameter name
    pub name: Ident,
    /// Type annotation (None if omitted for inference)
    pub ty: Option<TypeId>,
}

/// Constraint annotation (@requires)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Constraint {
    /// Source location of the constraint annotation
    pub span: Span,
    /// The kind of constraint (resource bound or predicate)
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
    /// Source location of the optimization objective
    pub span: Span,
    /// Whether to minimize or maximize the target
    pub direction: OptimizeDirection,
    /// Resource to optimize (e.g., `energy`, `latency`)
    pub target: Ident,
}

/// Optimization direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OptimizeDirection {
    /// Minimize the target resource (e.g., reduce energy usage)
    Minimize,
    /// Maximize the target resource (e.g., increase throughput)
    Maximize,
}

/// Comparison operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CompareOp {
    /// Less than (`<`)
    Lt,
    /// Less than or equal (`<=`)
    Le,
    /// Greater than (`>`)
    Gt,
    /// Greater than or equal (`>=`)
    Ge,
    /// Equal (`==`)
    Eq,
    /// Not equal (`!=`)
    Ne,
}

// === Trait Declaration ===

/// Trait declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TraitDecl {
    /// Source location of the trait declaration
    pub span: Span,
    /// Visibility modifier
    pub visibility: Visibility,
    /// Name of the trait
    pub name: Ident,
    /// Generic type parameters
    pub type_params: Vec<TypeParam>,
    /// Super-trait bounds that implementors must also satisfy
    pub super_traits: Vec<TraitBound>,
    /// Where clause constraints
    pub where_clause: Vec<WherePredicate>,
    /// Methods, associated types, and constants in the trait
    pub items: Vec<TraitItem>,
}

/// An item inside a trait declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TraitItem {
    /// Method signature (possibly with default body)
    Method {
        sig: FunctionSig,
        body: Option<Block>,
        attributes: Vec<Attribute>,
    },
    /// Associated type
    AssocType {
        span: Span,
        name: Ident,
        bounds: Vec<TraitBound>,
        default: Option<TypeId>,
    },
    /// Associated constant
    AssocConst {
        span: Span,
        name: Ident,
        ty: TypeId,
        default: Option<ExprId>,
    },
}

// === Impl Block ===

/// Implementation block
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImplBlock {
    /// Source location of the impl block
    pub span: Span,
    /// Generic type parameters for the impl block
    pub type_params: Vec<TypeParam>,
    /// The trait being implemented (None for inherent impls)
    pub trait_path: Option<Vec<Ident>>,
    /// The type being implemented for
    pub self_ty: TypeId,
    /// Where clause constraints
    pub where_clause: Vec<WherePredicate>,
    /// Methods, associated types, and constants in the impl block
    pub items: Vec<ImplItem>,
}

/// An item inside an impl block
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ImplItem {
    /// Method implementation
    Method {
        visibility: Visibility,
        sig: FunctionSig,
        body: Block,
        attributes: Vec<Attribute>,
    },
    /// Associated type definition
    AssocType {
        span: Span,
        name: Ident,
        ty: TypeId,
    },
    /// Associated constant definition
    AssocConst {
        span: Span,
        name: Ident,
        ty: TypeId,
        value: ExprId,
    },
}

// === Module Declaration ===

/// Module declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleDecl {
    /// Source location of the module declaration
    pub span: Span,
    /// Visibility modifier
    pub visibility: Visibility,
    /// Name of the module
    pub name: Ident,
    /// Inline module body (None means external file)
    pub items: Option<Vec<Item>>,
}

// === Effect Declaration ===

/// Effect declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EffectDecl {
    /// Source location of the effect declaration
    pub span: Span,
    /// Visibility modifier
    pub visibility: Visibility,
    /// Name of the effect
    pub name: Ident,
    /// Generic type parameters
    pub type_params: Vec<TypeParam>,
    /// Operations defined by this effect
    pub operations: Vec<EffectOp>,
}

/// An operation in an effect declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EffectOp {
    /// Source location of the effect operation
    pub span: Span,
    /// Name of the operation
    pub name: Ident,
    /// Parameters the operation accepts
    pub params: Vec<Param>,
    /// Return type of the operation (None for unit)
    pub return_type: Option<TypeId>,
}

/// An effect handler in a handle expression
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EffectHandler {
    /// Source location of the effect handler
    pub span: Span,
    /// Name of the effect being handled
    pub effect_name: Ident,
    /// Name of the operation being handled
    pub op_name: Ident,
    /// Parameters captured from the operation call
    pub params: Vec<Param>,
    /// Optional continuation parameter for resuming the computation
    pub resume_param: Option<Ident>,
    /// Handler body that processes the effect
    pub body: Block,
}

// === Static Declaration ===

/// Static variable declaration
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StaticDecl {
    /// Source location of the static declaration
    pub span: Span,
    /// Visibility modifier
    pub visibility: Visibility,
    /// Whether this static is mutable (`static mut`)
    pub mutable: bool,
    /// Name of the static variable
    pub name: Ident,
    /// Type of the static variable
    pub ty: TypeId,
    /// Initializer expression
    pub value: ExprId,
}

// === Extern Block ===

/// Extern block for foreign function declarations
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExternBlock {
    /// Source location of the extern block
    pub span: Span,
    /// ABI string (e.g., `"C"`, `"stdcall"`), None for default ABI
    pub abi: Option<Ident>,
    /// Foreign function and static declarations
    pub items: Vec<ExternItem>,
}

/// An item in an extern block
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExternItem {
    /// Foreign function declaration
    Fn(FunctionSig),
    /// Foreign static variable declaration
    Static {
        span: Span,
        mutable: bool,
        name: Ident,
        ty: TypeId,
    },
}

// === Macro Definition ===

/// Macro definition (declarative, hygienic)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MacroDef {
    /// Source location of the macro definition.
    pub span: Span,
    /// Visibility modifier.
    pub visibility: Visibility,
    /// Name of the macro.
    pub name: Ident,
    /// Macro rules (pattern → template pairs).
    pub rules: Vec<MacroRule>,
}

/// A single macro rule (pattern → template).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MacroRule {
    /// Source location of this rule.
    pub span: Span,
    /// Pattern tokens to match against invocation.
    pub pattern: Vec<MacroToken>,
    /// Template tokens to expand.
    pub template: Vec<MacroToken>,
}

/// A token in a macro pattern or template.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MacroToken {
    /// Literal token (keyword, punctuation, literal).
    Literal(Ident),
    /// Metavariable ($name:kind).
    MetaVar { name: Ident, kind: MacroVarKind },
    /// Repetition ($(...)*  or  $(...)+  or  $(...)?).
    Repetition {
        tokens: Vec<MacroToken>,
        separator: Option<Ident>,
        kind: RepetitionKind,
    },
}

/// Kind of macro metavariable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MacroVarKind {
    /// Expression.
    Expr,
    /// Statement.
    Stmt,
    /// Type.
    Ty,
    /// Pattern.
    Pat,
    /// Identifier.
    Ident,
    /// Block.
    Block,
    /// Literal.
    Literal,
    /// Token tree (any).
    Tt,
}

/// Kind of macro repetition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RepetitionKind {
    /// Zero or more (*).
    ZeroOrMore,
    /// One or more (+).
    OneOrMore,
    /// Zero or one (?).
    Optional,
}

// === Type Definition (unchanged but with visibility) ===

/// Type definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeDef {
    /// Source location of the type definition
    pub span: Span,
    /// Name of the type being defined
    pub name: Ident,
    /// Generic type parameter names
    pub params: Vec<Ident>,
    /// The kind of type being defined (alias, struct, or enum)
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
    /// Source location of the field
    pub span: Span,
    /// Field name
    pub name: Ident,
    /// Type of the field
    pub ty: TypeId,
}

/// Enum variant
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Variant {
    /// Source location of the variant
    pub span: Span,
    /// Variant name
    pub name: Ident,
    /// Payload types (None for unit variants, Some for tuple variants)
    pub fields: Option<Vec<TypeId>>,
}

/// Import statement
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Import {
    /// Source location of the import statement
    pub span: Span,
    /// Module path segments (e.g., `["std", "io", "read"]`)
    pub path: Vec<Ident>,
    /// Optional rename alias (`as` clause)
    pub alias: Option<Ident>,
}

/// Constant definition
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConstDef {
    /// Source location of the constant definition
    pub span: Span,
    /// Name of the constant
    pub name: Ident,
    /// Type annotation (None if inferred)
    pub ty: Option<TypeId>,
    /// Initializer expression (must be compile-time evaluable)
    pub value: ExprId,
}

/// A block of statements
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Block {
    /// Source location of the block
    pub span: Span,
    /// Statements within the block
    pub stmts: Vec<StmtId>,
    /// Optional trailing expression (block value)
    pub expr: Option<ExprId>,
}

/// Statement
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Stmt {
    /// Source location of the statement
    pub span: Span,
    /// The kind of statement
    pub kind: StmtKind,
}

/// Statement kind
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StmtKind {
    /// Let binding (with pattern support)
    Let {
        pattern: Pattern,
        mutable: bool,
        ty: Option<TypeId>,
        value: ExprId,
    },
    /// Assignment statement (target can be field/index expr)
    Assign {
        target: ExprId,
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
        pattern: Pattern,
        iter: ExprId,
        body: Block,
    },
    /// Infinite loop
    Loop {
        label: Option<Ident>,
        body: Block,
    },
    /// Break statement
    Break {
        label: Option<Ident>,
        value: Option<ExprId>,
    },
    /// Continue statement
    Continue {
        label: Option<Ident>,
    },
    /// Error placeholder for resilient parsing
    Error,
}

/// Expression
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expr {
    /// Source location of the expression
    pub span: Span,
    /// The kind of expression
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
    /// Array repeat [value; count]
    ArrayRepeat { value: ExprId, count: ExprId },
    /// Struct literal
    Struct {
        name: Ident,
        fields: Vec<(Ident, ExprId)>,
    },
    /// Resource literal (e.g., 100J, 5ms, 10gCO2e)
    Resource(ResourceAmount),
    /// Type cast (e.g., x as T)
    Cast {
        expr: ExprId,
        target_ty: TypeId,
    },
    /// Try operator (expr?)
    Try(ExprId),
    /// Borrow (&expr or &mut expr)
    Borrow { expr: ExprId, mutable: bool },
    /// Dereference (*expr)
    Deref(ExprId),
    /// Async block (async { ... })
    AsyncBlock(Block),
    /// Await expression (expr.await)
    Await(ExprId),
    /// Spawn expression (spawn { ... } or spawn expr)
    Spawn(ExprId),
    /// Channel creation (chan<T>() or chan<T>(capacity))
    Channel { elem_ty: Option<TypeId>, capacity: Option<ExprId> },
    /// Send on channel (send(ch, value))
    Send { channel: ExprId, value: ExprId },
    /// Receive from channel (recv(ch))
    Recv(ExprId),
    /// Select expression (select { ch1 => ..., ch2 => ... })
    Select { arms: Vec<SelectArm> },
    /// Yield expression (yield or yield value)
    YieldExpr(Option<ExprId>),
    /// Handle expression (handle expr { handlers })
    Handle {
        expr: ExprId,
        handlers: Vec<EffectHandler>,
    },
    /// Return as expression
    ReturnExpr(Option<ExprId>),
    /// Break as expression
    BreakExpr {
        label: Option<Ident>,
        value: Option<ExprId>,
    },
    /// Continue as expression
    ContinueExpr {
        label: Option<Ident>,
    },
    /// Path expression (e.g., Foo::bar)
    PathExpr(Vec<Ident>),
    /// Error placeholder for recovery
    Error,
}

/// Select arm for channel select expressions.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SelectArm {
    /// Source location of the select arm.
    pub span: Span,
    /// Channel expression to receive from.
    pub channel: ExprId,
    /// Variable to bind the received value.
    pub binding: Option<Ident>,
    /// Body expression to evaluate when this arm fires.
    pub body: ExprId,
}

/// Match arm
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MatchArm {
    /// Source location of the match arm
    pub span: Span,
    /// Pattern to match against the scrutinee
    pub pattern: Pattern,
    /// Optional guard expression (`if condition`)
    pub guard: Option<ExprId>,
    /// Body expression evaluated when the arm matches
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
    /// Constructor pattern (e.g., Some(x))
    Constructor { name: Ident, fields: Vec<Pattern> },
    /// Struct pattern (e.g., Point { x, y, .. })
    Struct {
        name: Ident,
        fields: Vec<FieldPattern>,
        rest: bool,
    },
    /// Slice pattern (e.g., [a, b, ..])
    Slice(Vec<Pattern>),
    /// Or pattern (e.g., a | b)
    Or(Vec<Pattern>),
    /// Range pattern (e.g., 1..=5)
    Range {
        start: Option<Box<Pattern>>,
        end: Option<Box<Pattern>>,
        inclusive: bool,
    },
    /// Rest pattern (..)
    Rest,
    /// Binding pattern (name @ pattern)
    Binding {
        name: Ident,
        pattern: Box<Pattern>,
    },
    /// Reference pattern (&pat or &mut pat)
    Reference {
        pattern: Box<Pattern>,
        mutable: bool,
    },
}

/// Field pattern inside a struct pattern
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FieldPattern {
    /// Source location of the field pattern
    pub span: Span,
    /// Field name being matched
    pub name: Ident,
    /// Sub-pattern for the field value (None uses shorthand binding)
    pub pattern: Option<Pattern>,
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
    /// Addition (`+`)
    Add,
    /// Subtraction (`-`)
    Sub,
    /// Multiplication (`*`)
    Mul,
    /// Division (`/`)
    Div,
    /// Remainder/modulo (`%`)
    Rem,
    /// Exponentiation (`**`)
    Pow,
    // Comparison
    /// Equality (`==`)
    Eq,
    /// Inequality (`!=`)
    Ne,
    /// Less than (`<`)
    Lt,
    /// Less than or equal (`<=`)
    Le,
    /// Greater than (`>`)
    Gt,
    /// Greater than or equal (`>=`)
    Ge,
    // Logical
    /// Logical AND (`&&`)
    And,
    /// Logical OR (`||`)
    Or,
    // Bitwise
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
    // Range
    /// Exclusive range (`..`)
    Range,
    /// Inclusive range (`..=`)
    RangeInclusive,
}

/// Unary operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    /// Arithmetic negation (`-x`)
    Neg,
    /// Logical negation (`!x`)
    Not,
    /// Bitwise complement (`~x`)
    BitNot,
}

/// Type expression
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Type {
    /// Source location of the type expression
    pub span: Span,
    /// The kind of type expression
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
    /// Reference type (&T or &mut T)
    Reference { ty: TypeId, mutable: bool },
    /// Optional type (T?)
    Optional(TypeId),
    /// Infer type (_)
    Infer,
    /// Error placeholder
    Error,
}
