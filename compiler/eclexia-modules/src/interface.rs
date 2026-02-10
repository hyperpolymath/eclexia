// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Module interface files (`.ecli`) for separate compilation.
//!
//! An interface file captures the public API of a module:
//! - Function signatures (name, params, return type)
//! - Type definitions (structs, enums, type aliases)
//! - Trait declarations
//! - Exported constants
//! - Resource constraint declarations
//!
//! Downstream modules only need the interface to type-check against
//! an upstream module, enabling separate compilation and faster
//! incremental rebuilds.

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::ModuleId;

/// A serialized module interface capturing the public API.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleInterface {
    /// Module identifier.
    pub module_id: String,
    /// Interface format version.
    pub version: u32,
    /// Exported function signatures.
    pub functions: Vec<FunctionSig>,
    /// Exported type definitions.
    pub types: Vec<TypeDef>,
    /// Exported trait declarations.
    pub traits: Vec<TraitSig>,
    /// Exported constants.
    pub constants: Vec<ConstantSig>,
    /// Module-level resource constraints.
    pub resource_constraints: Vec<ResourceConstraintSig>,
}

/// Current interface format version.
pub const INTERFACE_VERSION: u32 = 1;

/// A function signature in the interface.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSig {
    pub name: String,
    pub params: Vec<ParamSig>,
    pub return_type: String,
    pub type_params: Vec<String>,
    pub is_public: bool,
    pub is_adaptive: bool,
    pub resource_annotations: Vec<String>,
}

/// A parameter signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamSig {
    pub name: String,
    pub ty: String,
}

/// A type definition in the interface.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDef {
    pub name: String,
    pub kind: TypeDefKind,
    pub type_params: Vec<String>,
    pub is_public: bool,
}

/// Kind of type definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeDefKind {
    Struct { fields: Vec<FieldSig> },
    Enum { variants: Vec<VariantSig> },
    Alias { target: String },
}

/// A struct field signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldSig {
    pub name: String,
    pub ty: String,
    pub is_public: bool,
}

/// An enum variant signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariantSig {
    pub name: String,
    pub fields: Vec<FieldSig>,
}

/// A trait signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitSig {
    pub name: String,
    pub methods: Vec<FunctionSig>,
    pub type_params: Vec<String>,
    pub is_public: bool,
}

/// A constant signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstantSig {
    pub name: String,
    pub ty: String,
    pub is_public: bool,
}

/// A resource constraint signature.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceConstraintSig {
    pub resource: String,
    pub dimension: String,
    pub constraint: String,
}

impl ModuleInterface {
    /// Create a new empty module interface.
    pub fn new(module_id: &ModuleId) -> Self {
        Self {
            module_id: module_id.path.to_string(),
            version: INTERFACE_VERSION,
            functions: Vec::new(),
            types: Vec::new(),
            traits: Vec::new(),
            constants: Vec::new(),
            resource_constraints: Vec::new(),
        }
    }

    /// Generate a module interface from a parsed AST.
    ///
    /// Extracts the public API from the source file's items.
    pub fn from_ast(module_id: &ModuleId, file: &eclexia_ast::SourceFile) -> Self {
        let mut iface = Self::new(module_id);

        for item in &file.items {
            match item {
                eclexia_ast::Item::Function(func) => {
                    iface.functions.push(FunctionSig {
                        name: func.name.to_string(),
                        params: func
                            .params
                            .iter()
                            .map(|p| ParamSig {
                                name: p.name.to_string(),
                                ty: format!("{:?}", p.ty),
                            })
                            .collect(),
                        return_type: format!("{:?}", func.return_type),
                        type_params: func.type_params.iter().map(|t| t.to_string()).collect(),
                        is_public: true, // NOTE: visibility modifiers pending
                        is_adaptive: false,
                        resource_annotations: Vec::new(),
                    });
                }
                eclexia_ast::Item::AdaptiveFunction(func) => {
                    iface.functions.push(FunctionSig {
                        name: func.name.to_string(),
                        params: func
                            .params
                            .iter()
                            .map(|p| ParamSig {
                                name: p.name.to_string(),
                                ty: format!("{:?}", p.ty),
                            })
                            .collect(),
                        return_type: format!("{:?}", func.return_type),
                        type_params: func.type_params.iter().map(|t| t.to_string()).collect(),
                        is_public: true,
                        is_adaptive: true,
                        resource_annotations: Vec::new(),
                    });
                }
                eclexia_ast::Item::TypeDef(typedef) => {
                    let kind = match &typedef.kind {
                        eclexia_ast::TypeDefKind::Alias(ty) => TypeDefKind::Alias {
                            target: format!("{:?}", ty),
                        },
                        eclexia_ast::TypeDefKind::Struct(fields) => TypeDefKind::Struct {
                            fields: fields
                                .iter()
                                .map(|f| FieldSig {
                                    name: f.name.to_string(),
                                    ty: format!("{:?}", f.ty),
                                    is_public: true,
                                })
                                .collect(),
                        },
                        eclexia_ast::TypeDefKind::Enum(variants) => TypeDefKind::Enum {
                            variants: variants
                                .iter()
                                .map(|v| VariantSig {
                                    name: v.name.to_string(),
                                    fields: v
                                        .fields
                                        .as_ref()
                                        .map(|fs| {
                                            fs.iter()
                                                .enumerate()
                                                .map(|(i, ty)| FieldSig {
                                                    name: format!("_{i}"),
                                                    ty: format!("{ty:?}"),
                                                    is_public: true,
                                                })
                                                .collect()
                                        })
                                        .unwrap_or_default(),
                                })
                                .collect(),
                        },
                    };
                    iface.types.push(TypeDef {
                        name: typedef.name.to_string(),
                        kind,
                        type_params: typedef.params.iter().map(|t| t.to_string()).collect(),
                        is_public: true,
                    });
                }
                eclexia_ast::Item::TraitDecl(trait_decl) => {
                    let methods = trait_decl
                        .items
                        .iter()
                        .filter_map(|item| {
                            if let eclexia_ast::TraitItem::Method { sig, .. } = item {
                                Some(FunctionSig {
                                    name: sig.name.to_string(),
                                    params: sig
                                        .params
                                        .iter()
                                        .map(|p| ParamSig {
                                            name: p.name.to_string(),
                                            ty: format!("{:?}", p.ty),
                                        })
                                        .collect(),
                                    return_type: format!("{:?}", sig.return_type),
                                    type_params: sig
                                        .type_params
                                        .iter()
                                        .map(|t| t.name.to_string())
                                        .collect(),
                                    is_public: true,
                                    is_adaptive: false,
                                    resource_annotations: Vec::new(),
                                })
                            } else {
                                None
                            }
                        })
                        .collect();
                    iface.traits.push(TraitSig {
                        name: trait_decl.name.to_string(),
                        methods,
                        type_params: trait_decl
                            .type_params
                            .iter()
                            .map(|t| t.name.to_string())
                            .collect(),
                        is_public: true,
                    });
                }
                eclexia_ast::Item::Const(const_def) => {
                    iface.constants.push(ConstantSig {
                        name: const_def.name.to_string(),
                        ty: format!("{:?}", const_def.ty),
                        is_public: true,
                    });
                }
                // Skip imports, impl blocks, modules, effects, statics, externs
                _ => {}
            }
        }

        iface
    }

    /// Serialize the interface to JSON.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize an interface from JSON.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Write the interface to a `.ecli` file.
    pub fn write_to_file(&self, path: &Path) -> std::io::Result<()> {
        let json = self.to_json().map_err(|e| std::io::Error::other(e))?;
        std::fs::write(path, json)
    }

    /// Read an interface from a `.ecli` file.
    pub fn read_from_file(path: &Path) -> std::io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        Self::from_json(&json).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    /// Get the `.ecli` file path for a module.
    pub fn interface_path(module_id: &ModuleId, build_dir: &Path) -> std::path::PathBuf {
        let mut path = build_dir.join(module_id.to_file_path());
        path.set_extension("ecli");
        path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interface_roundtrip() {
        let module_id = ModuleId::new("test.module");
        let mut iface = ModuleInterface::new(&module_id);

        iface.functions.push(FunctionSig {
            name: "greet".to_string(),
            params: vec![ParamSig {
                name: "name".to_string(),
                ty: "String".to_string(),
            }],
            return_type: "Unit".to_string(),
            type_params: vec![],
            is_public: true,
            is_adaptive: false,
            resource_annotations: vec![],
        });

        let json = iface.to_json().unwrap();
        let restored = ModuleInterface::from_json(&json).unwrap();

        assert_eq!(restored.module_id, "test.module");
        assert_eq!(restored.functions.len(), 1);
        assert_eq!(restored.functions[0].name, "greet");
    }
}
