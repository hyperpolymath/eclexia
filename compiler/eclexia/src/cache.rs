// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Local package cache management.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

/// Package cache index (stores name-version -> path mappings).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct CacheIndex {
    packages: HashMap<String, PathBuf>,
}

/// Local package cache.
pub struct Cache {
    cache_dir: PathBuf,
    index_path: PathBuf,
    index: CacheIndex,
}

impl Cache {
    /// Create a new cache at the given directory.
    pub fn new(cache_dir: PathBuf) -> Result<Self, String> {
        // Create cache directory if it doesn't exist
        fs::create_dir_all(&cache_dir)
            .map_err(|e| format!("Failed to create cache directory: {}", e))?;

        let index_path = cache_dir.join("cache.json");

        // Load or create index
        let index = if index_path.exists() {
            let content = fs::read_to_string(&index_path)
                .map_err(|e| format!("Failed to read cache index: {}", e))?;
            serde_json::from_str(&content)
                .map_err(|e| format!("Failed to parse cache index: {}", e))?
        } else {
            CacheIndex::default()
        };

        Ok(Self {
            cache_dir,
            index_path,
            index,
        })
    }

    /// Check if a package is cached.
    pub fn has(&self, name: &str, version: &str) -> bool {
        let key = format!("{}@{}", name, version);
        self.index.packages.contains_key(&key)
    }

    /// Get the path to a cached package.
    pub fn get(&self, name: &str, version: &str) -> Option<PathBuf> {
        let key = format!("{}@{}", name, version);
        self.index.packages.get(&key).cloned()
    }

    /// Add a package to the cache.
    pub fn add(&mut self, name: &str, version: &str, path: PathBuf) -> Result<(), String> {
        let key = format!("{}@{}", name, version);
        self.index.packages.insert(key, path);

        // Save index
        self.save_index()
    }

    /// Get the directory for storing a specific package.
    pub fn package_dir(&self, name: &str, version: &str) -> PathBuf {
        self.cache_dir.join(format!("{}-{}", name, version))
    }

    /// Save the cache index to disk.
    fn save_index(&self) -> Result<(), String> {
        let content = serde_json::to_string_pretty(&self.index)
            .map_err(|e| format!("Failed to serialize cache index: {}", e))?;

        fs::write(&self.index_path, content)
            .map_err(|e| format!("Failed to write cache index: {}", e))?;

        Ok(())
    }
}

impl Default for Cache {
    fn default() -> Self {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let cache_dir = PathBuf::from(home).join(".eclexia").join("cache");
        Self::new(cache_dir).expect("Failed to create default cache")
    }
}
