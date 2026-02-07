// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! High-level package manager orchestration.

use crate::cache::Cache;
use crate::lockfile::LockFile;
use crate::package::PackageManifest;
use crate::registry::RegistryClient;
use crate::resolver::resolve_dependencies;
use std::collections::HashMap;
use std::path::Path;

/// Package manager for installing dependencies.
pub struct PackageManager {
    registry: RegistryClient,
    cache: Cache,
}

impl PackageManager {
    /// Create a new package manager.
    pub fn new() -> Result<Self, String> {
        Ok(Self {
            registry: RegistryClient::default(),
            cache: Cache::default(),
        })
    }

    /// Install dependencies from a package manifest.
    pub fn install(&mut self, manifest: &PackageManifest) -> Result<(), String> {
        println!("Resolving dependencies...");

        // Step 1: Resolve dependencies
        let resolved = resolve_dependencies(&manifest.dependencies)?;

        println!("Resolved {} packages", resolved.len());

        // Step 2: Download packages (use cache if available)
        let mut checksums = HashMap::new();

        for (name, version) in &resolved {
            println!("Installing {}@{}...", name, version);

            // Check if already cached
            if self.cache.has(name, version) {
                println!("  Using cached version");
                continue;
            }

            // Fetch metadata from registry
            let metadata = self.registry.fetch_metadata(name, version)?;

            // Download tarball
            let package_dir = self.cache.package_dir(name, version);
            let tarball_path = package_dir.with_extension("tar.gz");

            // Create parent directory for tarball
            if let Some(parent) = tarball_path.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| format!("Failed to create tarball directory: {}", e))?;
            }

            self.registry.download_package(&metadata, &tarball_path)?;

            // Extract tarball
            RegistryClient::extract_tarball(&tarball_path, &package_dir)?;

            // Add to cache
            self.cache.add(name, version, package_dir.clone())?;

            // Store checksum for lock file
            checksums.insert(
                format!("{}@{}", name, version),
                metadata.checksum.clone(),
            );

            println!("  Installed to {}", package_dir.display());
        }

        // Step 3: Generate lock file
        println!("Generating package.lock...");
        let lock_file = LockFile::from_resolved(&resolved, &checksums);
        lock_file.save(Path::new("package.lock"))?;

        println!("Installation complete!");

        Ok(())
    }
}

impl Default for PackageManager {
    fn default() -> Self {
        Self::new().expect("Failed to create package manager")
    }
}
