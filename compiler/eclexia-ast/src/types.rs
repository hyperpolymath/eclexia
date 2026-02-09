// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Type representations for the Eclexia type system.
//!
//! This module defines the semantic types used during type checking,
//! separate from the syntactic type expressions in the AST.

use crate::dimension::Dimension;
use smol_str::SmolStr;

/// A semantic type in Eclexia's type system.
#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    /// Primitive types
    Primitive(PrimitiveTy),

    /// A named type (struct, enum, alias) with optional type arguments
    Named {
        name: SmolStr,
        args: Vec<Ty>,
    },

    /// Function type
    Function {
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    /// Tuple type
    Tuple(Vec<Ty>),

    /// Array type
    Array {
        elem: Box<Ty>,
        size: Option<usize>,
    },

    /// Resource-annotated type with dimensional information
    Resource {
        base: PrimitiveTy,
        dimension: Dimension,
    },

    /// Type variable (for inference)
    Var(TypeVar),

    /// Universal quantification (polymorphic type)
    ForAll {
        vars: Vec<SmolStr>,
        body: Box<Ty>,
    },

    /// Error type (for recovery)
    Error,

    /// Never type (for diverging expressions)
    Never,
}

impl Ty {
    /// Check if this type contains any type variables.
    pub fn has_vars(&self) -> bool {
        match self {
            Ty::Var(_) => true,
            Ty::Named { args, .. } => args.iter().any(|t| t.has_vars()),
            Ty::Function { params, ret } => {
                params.iter().any(|t| t.has_vars()) || ret.has_vars()
            }
            Ty::Tuple(elems) => elems.iter().any(|t| t.has_vars()),
            Ty::Array { elem, .. } => elem.has_vars(),
            Ty::ForAll { body, .. } => body.has_vars(),
            _ => false,
        }
    }

    /// Check if this type is dimensioned (has resource tracking).
    pub fn is_resource(&self) -> bool {
        matches!(self, Ty::Resource { .. })
    }

    /// Get the dimension if this is a resource type.
    pub fn dimension(&self) -> Option<&Dimension> {
        match self {
            Ty::Resource { dimension, .. } => Some(dimension),
            _ => None,
        }
    }

    /// Create a unit type.
    pub fn unit() -> Self {
        Ty::Tuple(Vec::new())
    }

    /// Create an integer type.
    pub fn int() -> Self {
        Ty::Primitive(PrimitiveTy::Int)
    }

    /// Create a float type.
    pub fn float() -> Self {
        Ty::Primitive(PrimitiveTy::Float)
    }

    /// Create a bool type.
    pub fn bool() -> Self {
        Ty::Primitive(PrimitiveTy::Bool)
    }

    /// Create a string type.
    pub fn string() -> Self {
        Ty::Primitive(PrimitiveTy::String)
    }
}

/// Primitive types built into the language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    /// Signed integer (platform-dependent size)
    Int,
    /// 8-bit signed integer
    I8,
    /// 16-bit signed integer
    I16,
    /// 32-bit signed integer
    I32,
    /// 64-bit signed integer
    I64,
    /// 128-bit signed integer
    I128,
    /// Unsigned integer (platform-dependent size)
    UInt,
    /// 8-bit unsigned integer
    U8,
    /// 16-bit unsigned integer
    U16,
    /// 32-bit unsigned integer
    U32,
    /// 64-bit unsigned integer
    U64,
    /// 128-bit unsigned integer
    U128,
    /// 32-bit floating point
    F32,
    /// 64-bit floating point
    F64,
    /// Default float type (F64)
    Float,
    /// Boolean
    Bool,
    /// Unicode character
    Char,
    /// String type
    String,
    /// Unit type (void)
    Unit,
}

impl PrimitiveTy {
    /// Get the name of this primitive type.
    pub fn name(&self) -> &'static str {
        match self {
            PrimitiveTy::Int => "Int",
            PrimitiveTy::I8 => "I8",
            PrimitiveTy::I16 => "I16",
            PrimitiveTy::I32 => "I32",
            PrimitiveTy::I64 => "I64",
            PrimitiveTy::I128 => "I128",
            PrimitiveTy::UInt => "UInt",
            PrimitiveTy::U8 => "U8",
            PrimitiveTy::U16 => "U16",
            PrimitiveTy::U32 => "U32",
            PrimitiveTy::U64 => "U64",
            PrimitiveTy::U128 => "U128",
            PrimitiveTy::F32 => "F32",
            PrimitiveTy::F64 => "F64",
            PrimitiveTy::Float => "Float",
            PrimitiveTy::Bool => "Bool",
            PrimitiveTy::Char => "Char",
            PrimitiveTy::String => "String",
            PrimitiveTy::Unit => "Unit",
        }
    }

    /// Check if this is a numeric type.
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            PrimitiveTy::Int
                | PrimitiveTy::I8
                | PrimitiveTy::I16
                | PrimitiveTy::I32
                | PrimitiveTy::I64
                | PrimitiveTy::I128
                | PrimitiveTy::UInt
                | PrimitiveTy::U8
                | PrimitiveTy::U16
                | PrimitiveTy::U32
                | PrimitiveTy::U64
                | PrimitiveTy::U128
                | PrimitiveTy::F32
                | PrimitiveTy::F64
                | PrimitiveTy::Float
        )
    }

    /// Check if this is an integer type.
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            PrimitiveTy::Int
                | PrimitiveTy::I8
                | PrimitiveTy::I16
                | PrimitiveTy::I32
                | PrimitiveTy::I64
                | PrimitiveTy::I128
                | PrimitiveTy::UInt
                | PrimitiveTy::U8
                | PrimitiveTy::U16
                | PrimitiveTy::U32
                | PrimitiveTy::U64
                | PrimitiveTy::U128
        )
    }

    /// Check if this is a floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(
            self,
            PrimitiveTy::F32 | PrimitiveTy::F64 | PrimitiveTy::Float
        )
    }
}

/// A type variable for type inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(pub u32);

impl TypeVar {
    /// Create a new type variable with the given ID.
    pub const fn new(id: u32) -> Self {
        Self(id)
    }
}

/// Type scheme for polymorphic types.
#[derive(Debug, Clone)]
pub struct TypeScheme {
    /// Bound type variables
    pub vars: Vec<SmolStr>,
    /// The body type
    pub ty: Ty,
}

impl TypeScheme {
    /// Create a monomorphic type scheme (no quantification).
    pub fn mono(ty: Ty) -> Self {
        Self {
            vars: Vec::new(),
            ty,
        }
    }

    /// Check if this scheme is monomorphic.
    pub fn is_mono(&self) -> bool {
        self.vars.is_empty()
    }
}

/// Resource constraint for type checking.
#[derive(Debug, Clone)]
pub struct ResourceConstraint {
    /// The resource being constrained (energy, time, memory, carbon)
    pub resource: SmolStr,
    /// The dimension of the resource
    pub dimension: Dimension,
    /// The constraint operator
    pub op: ConstraintOp,
    /// The bound value
    pub bound: f64,
}

/// Constraint operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintOp {
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
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Primitive(p) => write!(f, "{}", p.name()),
            Ty::Named { name, args } => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "[")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Ty::Function { params, ret } => {
                write!(f, "(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ret)
            }
            Ty::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                if elems.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            Ty::Array { elem, size } => {
                write!(f, "[{}]", elem)?;
                if let Some(n) = size {
                    write!(f, "; {}", n)?;
                }
                Ok(())
            }
            Ty::Resource { base, dimension } => {
                write!(f, "{}[{}]", base.name(), dimension)
            }
            Ty::Var(v) => write!(f, "?{}", v.0),
            Ty::ForAll { vars, body } => {
                write!(f, "∀")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, ". {}", body)
            }
            Ty::Error => write!(f, "{{error}}"),
            Ty::Never => write!(f, "!"),
        }
    }
}
