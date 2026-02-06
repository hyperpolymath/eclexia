// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Cranelift JIT backend.
//!
//! Provides fast JIT compilation to native code using Cranelift.
//! This is a future enhancement for performance-critical paths.

use crate::{Backend, CodegenError};
use eclexia_mir::MirFile;

/// Cranelift JIT backend
pub struct CraneliftBackend {
    // TODO: Cranelift context and module
}

impl CraneliftBackend {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for CraneliftBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for CraneliftBackend {
    type Output = Vec<u8>; // Native code bytes

    fn generate(&mut self, _mir: &MirFile) -> Result<Self::Output, CodegenError> {
        // TODO: Implement Cranelift code generation
        Err(CodegenError::UnsupportedFeature(
            "Cranelift backend not yet implemented".to_string()
        ))
    }

    fn name(&self) -> &str {
        "cranelift"
    }
}
