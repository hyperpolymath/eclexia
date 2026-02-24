// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Runtime environment for variable bindings.

use crate::Value;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::cell::RefCell;
use std::rc::Rc;

/// Runtime environment for variable bindings.
#[derive(Debug, Clone)]
pub struct Environment {
    inner: Rc<RefCell<EnvInner>>,
}

#[derive(Debug)]
struct EnvInner {
    bindings: FxHashMap<SmolStr, Value>,
    parent: Option<Environment>,
}

impl Environment {
    /// Create a new empty environment.
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(EnvInner {
                bindings: FxHashMap::default(),
                parent: None,
            })),
        }
    }

    /// Create a child environment with this as parent.
    pub fn child(&self) -> Self {
        Self {
            inner: Rc::new(RefCell::new(EnvInner {
                bindings: FxHashMap::default(),
                parent: Some(self.clone()),
            })),
        }
    }

    /// Define a new variable in this environment.
    pub fn define(&self, name: SmolStr, value: Value) {
        self.inner.borrow_mut().bindings.insert(name, value);
    }

    /// Look up a variable, searching parent scopes.
    pub fn get(&self, name: &str) -> Option<Value> {
        let inner = self.inner.borrow();
        if let Some(value) = inner.bindings.get(name) {
            Some(value.clone())
        } else if let Some(parent) = &inner.parent {
            parent.get(name)
        } else {
            None
        }
    }

    /// Assign to an existing variable, searching parent scopes.
    pub fn assign(&self, name: &str, value: Value) -> bool {
        // First check if it exists locally
        {
            let inner = self.inner.borrow();
            if inner.bindings.contains_key(name) {
                drop(inner);
                self.inner
                    .borrow_mut()
                    .bindings
                    .insert(SmolStr::new(name), value);
                return true;
            }
        }
        // Check parent scopes
        let parent = self.inner.borrow().parent.clone();
        if let Some(parent) = parent {
            parent.assign(name, value)
        } else {
            false
        }
    }

    /// Check if a variable is defined in this scope (not parents).
    pub fn has_local(&self, name: &str) -> bool {
        self.inner.borrow().bindings.contains_key(name)
    }

    /// Get all local bindings (for debugging).
    pub fn locals(&self) -> Vec<(SmolStr, Value)> {
        self.inner
            .borrow()
            .bindings
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
