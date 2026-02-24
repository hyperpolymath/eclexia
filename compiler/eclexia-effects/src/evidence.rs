// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Evidence-passing translation for algebraic effects.
//!
//! Transforms handle expressions into evidence vector construction
//! and effect operations into indirect calls through the evidence.
//!
//! ## Translation scheme
//!
//! ```text
//! handle expr {
//!     Console.print(msg) -> resume(()) { println(msg); resume(()) }
//! }
//! ```
//!
//! Becomes (conceptually):
//! ```text
//! let ev = EvidenceVector::new();
//! ev.push(EvidenceEntry { effect: "Console", op: "print", handler: |msg, resume| { ... } });
//! expr_with_evidence(ev)
//! ```

use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::{EffectSignature, EvidenceEntry, EvidenceVector};

/// Registry of known effect signatures.
#[derive(Debug, Clone)]
pub struct EffectRegistry {
    /// Map from effect name to its signature.
    effects: FxHashMap<SmolStr, EffectSignature>,
    /// Global index counter for evidence entries.
    next_index: usize,
}

impl EffectRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self {
            effects: FxHashMap::default(),
            next_index: 0,
        }
    }

    /// Register an effect signature.
    pub fn register(&mut self, sig: EffectSignature) {
        self.effects.insert(sig.name.clone(), sig);
    }

    /// Look up an effect by name.
    pub fn get(&self, name: &str) -> Option<&EffectSignature> {
        self.effects.get(name)
    }

    /// Check if an effect is registered.
    pub fn contains(&self, name: &str) -> bool {
        self.effects.contains_key(name)
    }

    /// Number of registered effects.
    pub fn len(&self) -> usize {
        self.effects.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    /// Build an evidence vector for a set of handler bindings.
    ///
    /// Each binding is `(effect_name, operation_name)`.
    /// Returns `None` if any binding references an unknown effect or operation.
    pub fn build_evidence(&mut self, bindings: &[(SmolStr, SmolStr)]) -> Option<EvidenceVector> {
        let mut ev = EvidenceVector::new();

        for (effect_name, op_name) in bindings {
            let sig = self.effects.get(effect_name)?;
            // Verify the operation exists in the effect
            if !sig.operations.iter().any(|op| op.name == *op_name) {
                return None;
            }

            let index = self.next_index;
            self.next_index += 1;

            ev.push(EvidenceEntry {
                effect: effect_name.clone(),
                operation: op_name.clone(),
                index,
            });
        }

        Some(ev)
    }

    /// Get the list of all registered effect names.
    pub fn effect_names(&self) -> Vec<SmolStr> {
        self.effects.keys().cloned().collect()
    }
}

impl Default for EffectRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of evidence-passing translation for a handle expression.
#[derive(Debug, Clone)]
pub struct TranslatedHandle {
    /// The evidence vector for this handler scope.
    pub evidence: EvidenceVector,
    /// Whether all required operations are handled.
    pub is_complete: bool,
    /// Missing operations (if incomplete).
    pub missing_ops: Vec<(SmolStr, SmolStr)>,
}

/// Check if a handle expression provides complete coverage
/// for the effects it claims to handle.
pub fn check_handler_completeness(
    registry: &EffectRegistry,
    handled_effects: &[SmolStr],
    provided_ops: &[(SmolStr, SmolStr)],
) -> TranslatedHandle {
    let mut missing_ops = Vec::new();
    let mut ev = EvidenceVector::new();
    let mut index = 0;

    for effect_name in handled_effects {
        if let Some(sig) = registry.get(effect_name) {
            for op in &sig.operations {
                if provided_ops
                    .iter()
                    .any(|(e, o)| e == effect_name && o == &op.name)
                {
                    ev.push(EvidenceEntry {
                        effect: effect_name.clone(),
                        operation: op.name.clone(),
                        index,
                    });
                    index += 1;
                } else {
                    missing_ops.push((effect_name.clone(), op.name.clone()));
                }
            }
        }
    }

    let is_complete = missing_ops.is_empty();
    TranslatedHandle {
        evidence: ev,
        is_complete,
        missing_ops,
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
    use crate::OperationSignature;

    fn make_console_effect() -> EffectSignature {
        EffectSignature {
            name: SmolStr::new("Console"),
            type_params: vec![],
            operations: vec![
                OperationSignature {
                    name: SmolStr::new("print"),
                    param_types: vec![SmolStr::new("msg")],
                    return_type: None,
                },
                OperationSignature {
                    name: SmolStr::new("read"),
                    param_types: vec![],
                    return_type: Some(SmolStr::new("String")),
                },
            ],
        }
    }

    fn make_state_effect() -> EffectSignature {
        EffectSignature {
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
        }
    }

    #[test]
    fn test_registry_register_and_get() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        assert!(reg.contains("Console"));
        assert!(!reg.contains("IO"));
        assert_eq!(reg.len(), 1);

        let sig = expect_some(reg.get("Console"), "expected Console signature");
        assert_eq!(sig.operations.len(), 2);
    }

    #[test]
    fn test_registry_multiple_effects() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());
        reg.register(make_state_effect());

        assert_eq!(reg.len(), 2);
        assert!(reg.contains("Console"));
        assert!(reg.contains("State"));
    }

    #[test]
    fn test_build_evidence_valid() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        let bindings = vec![
            (SmolStr::new("Console"), SmolStr::new("print")),
            (SmolStr::new("Console"), SmolStr::new("read")),
        ];

        let ev = expect_some(reg.build_evidence(&bindings), "expected evidence");
        assert_eq!(ev.len(), 2);
        assert!(ev.lookup("Console", "print").is_some());
        assert!(ev.lookup("Console", "read").is_some());
    }

    #[test]
    fn test_build_evidence_unknown_effect() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        let bindings = vec![(SmolStr::new("Unknown"), SmolStr::new("op"))];
        assert!(reg.build_evidence(&bindings).is_none());
    }

    #[test]
    fn test_build_evidence_unknown_operation() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        let bindings = vec![(SmolStr::new("Console"), SmolStr::new("write"))];
        assert!(reg.build_evidence(&bindings).is_none());
    }

    #[test]
    fn test_handler_completeness_complete() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        let handled = vec![SmolStr::new("Console")];
        let provided = vec![
            (SmolStr::new("Console"), SmolStr::new("print")),
            (SmolStr::new("Console"), SmolStr::new("read")),
        ];

        let result = check_handler_completeness(&reg, &handled, &provided);
        assert!(result.is_complete);
        assert!(result.missing_ops.is_empty());
        assert_eq!(result.evidence.len(), 2);
    }

    #[test]
    fn test_handler_completeness_incomplete() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());

        let handled = vec![SmolStr::new("Console")];
        let provided = vec![(SmolStr::new("Console"), SmolStr::new("print"))];

        let result = check_handler_completeness(&reg, &handled, &provided);
        assert!(!result.is_complete);
        assert_eq!(result.missing_ops.len(), 1);
        assert_eq!(result.missing_ops[0].1, "read");
    }

    #[test]
    fn test_handler_completeness_multiple_effects() {
        let mut reg = EffectRegistry::new();
        reg.register(make_console_effect());
        reg.register(make_state_effect());

        let handled = vec![SmolStr::new("Console"), SmolStr::new("State")];
        let provided = vec![
            (SmolStr::new("Console"), SmolStr::new("print")),
            (SmolStr::new("Console"), SmolStr::new("read")),
            (SmolStr::new("State"), SmolStr::new("get")),
            (SmolStr::new("State"), SmolStr::new("set")),
        ];

        let result = check_handler_completeness(&reg, &handled, &provided);
        assert!(result.is_complete);
        assert_eq!(result.evidence.len(), 4);
    }
}
