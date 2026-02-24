// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Algebraic effect compilation for Eclexia.
//!
//! Implements evidence-passing translation (Koka-style) for algebraic
//! effects and handlers. Each effect operation becomes a call through
//! an evidence vector, and handlers install evidence entries.
//!
//! ## Architecture
//!
//! ```text
//! AST EffectDecl → EffectSignature (registry)
//! AST Handle expr → evidence vector construction + operation calls
//! ```
//!
//! ## Key concepts
//!
//! - **Effect signature**: Declares available operations for an effect
//! - **Evidence vector**: Runtime dispatch table for effect operations
//! - **Evidence entry**: A single operation implementation (handler)
//! - **Row polymorphism**: Track which effects a function may perform

pub mod evidence;
pub mod row;

use smol_str::SmolStr;

/// An effect signature declaring available operations.
#[derive(Debug, Clone)]
pub struct EffectSignature {
    /// Effect name.
    pub name: SmolStr,
    /// Type parameters for the effect.
    pub type_params: Vec<SmolStr>,
    /// Operations declared by this effect.
    pub operations: Vec<OperationSignature>,
}

/// Signature of a single effect operation.
#[derive(Debug, Clone)]
pub struct OperationSignature {
    /// Operation name.
    pub name: SmolStr,
    /// Parameter type descriptors.
    pub param_types: Vec<SmolStr>,
    /// Return type descriptor (None = unit).
    pub return_type: Option<SmolStr>,
}

/// An evidence entry binding an operation to a handler.
#[derive(Debug, Clone)]
pub struct EvidenceEntry {
    /// Effect name this entry handles.
    pub effect: SmolStr,
    /// Operation name.
    pub operation: SmolStr,
    /// Index in the evidence vector.
    pub index: usize,
}

/// A compiled evidence vector for a handler scope.
#[derive(Debug, Clone)]
pub struct EvidenceVector {
    /// Handler entries, indexed by operation.
    pub entries: Vec<EvidenceEntry>,
}

impl EvidenceVector {
    /// Create an empty evidence vector.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Add an evidence entry.
    pub fn push(&mut self, entry: EvidenceEntry) {
        self.entries.push(entry);
    }

    /// Look up an operation in the evidence vector.
    pub fn lookup(&self, effect: &str, operation: &str) -> Option<&EvidenceEntry> {
        self.entries
            .iter()
            .find(|e| e.effect == effect && e.operation == operation)
    }

    /// Number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

impl Default for EvidenceVector {
    fn default() -> Self {
        Self::new()
    }
}

/// Build an effect signature from an AST effect declaration.
pub fn effect_signature_from_decl(decl: &eclexia_ast::EffectDecl) -> EffectSignature {
    let operations = decl
        .operations
        .iter()
        .map(|op| OperationSignature {
            name: op.name.clone(),
            param_types: op.params.iter().map(|p| p.name.clone()).collect(),
            return_type: op.return_type.map(|_| SmolStr::new("_")),
        })
        .collect();

    EffectSignature {
        name: decl.name.clone(),
        type_params: decl.type_params.iter().map(|tp| tp.name.clone()).collect(),
        operations,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_some<T>(value: Option<T>, context: &str) -> T {
        match value {
            Some(val) => val,
            None => panic!("Expected Some value: {}", context),
        }
    }

    #[test]
    fn test_evidence_vector_new() {
        let ev = EvidenceVector::new();
        assert!(ev.is_empty());
        assert_eq!(ev.len(), 0);
    }

    #[test]
    fn test_evidence_vector_push_and_lookup() {
        let mut ev = EvidenceVector::new();
        ev.push(EvidenceEntry {
            effect: SmolStr::new("Console"),
            operation: SmolStr::new("print"),
            index: 0,
        });
        ev.push(EvidenceEntry {
            effect: SmolStr::new("Console"),
            operation: SmolStr::new("read"),
            index: 1,
        });

        assert_eq!(ev.len(), 2);
        assert!(!ev.is_empty());

        let entry = expect_some(ev.lookup("Console", "print"), "print entry");
        assert_eq!(entry.index, 0);

        let entry = expect_some(ev.lookup("Console", "read"), "read entry");
        assert_eq!(entry.index, 1);

        assert!(ev.lookup("Console", "write").is_none());
        assert!(ev.lookup("IO", "print").is_none());
    }

    #[test]
    fn test_effect_signature() {
        let sig = EffectSignature {
            name: SmolStr::new("State"),
            type_params: vec![SmolStr::new("S")],
            operations: vec![
                OperationSignature {
                    name: SmolStr::new("get"),
                    param_types: vec![],
                    return_type: Some(SmolStr::new("S")),
                },
                OperationSignature {
                    name: SmolStr::new("set"),
                    param_types: vec![SmolStr::new("s")],
                    return_type: None,
                },
            ],
        };

        assert_eq!(sig.name, "State");
        assert_eq!(sig.type_params.len(), 1);
        assert_eq!(sig.operations.len(), 2);
        assert_eq!(sig.operations[0].name, "get");
        assert!(sig.operations[0].return_type.is_some());
        assert_eq!(sig.operations[1].name, "set");
        assert!(sig.operations[1].return_type.is_none());
    }
}
