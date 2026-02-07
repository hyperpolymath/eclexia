// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Lock file generation and management.

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use serde::{Deserialize, Serialize};

/// Lock file entry for a single package.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockEntry {
    pub name: String,
    pub version: String,
    pub checksum: String,
}

/// Lock file containing all resolved dependencies.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LockFile {
    #[serde(rename = "package")]
    pub packages: Vec<LockEntry>,
}

impl LockFile {
    /// Create a lock file from resolved packages.
    pub fn from_resolved(
        packages: &[(String, String)],
        checksums: &HashMap<String, String>,
    ) -> Self {
        let entries = packages
            .iter()
            .map(|(name, version)| {
                let key = format!("{}@{}", name, version);
                let checksum = checksums
                    .get(&key)
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_string());

                LockEntry {
                    name: name.clone(),
                    version: version.clone(),
                    checksum,
                }
            })
            .collect();

        Self { packages: entries }
    }

    /// Load lock file from path.
    pub fn load(path: &Path) -> Result<Self, String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read lock file: {}", e))?;

        toml::from_str(&content)
            .map_err(|e| format!("Failed to parse lock file: {}", e))
    }

    /// Save lock file to path.
    pub fn save(&self, path: &Path) -> Result<(), String> {
        let content = toml::to_string_pretty(self)
            .map_err(|e| format!("Failed to serialize lock file: {}", e))?;

        fs::write(path, content)
            .map_err(|e| format!("Failed to write lock file: {}", e))?;

        Ok(())
    }
}
