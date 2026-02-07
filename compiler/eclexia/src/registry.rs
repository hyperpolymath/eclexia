// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! HTTP registry client for package downloads.

use std::io::Write;
use std::path::Path;
use reqwest::blocking::Client;
use serde::{Deserialize, Serialize};
use sha2::{Sha256, Digest};

/// Package metadata from registry.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageMetadata {
    pub name: String,
    pub version: String,
    pub tarball_url: String,
    pub checksum: String,
}

/// HTTP registry client.
pub struct RegistryClient {
    base_url: String,
    client: Client,
}

impl RegistryClient {
    /// Create a new registry client with the given base URL.
    pub fn new(base_url: String) -> Self {
        Self {
            base_url,
            client: Client::new(),
        }
    }

    /// Fetch package metadata from the registry.
    pub fn fetch_metadata(&self, name: &str, version: &str) -> Result<PackageMetadata, String> {
        let url = format!("{}/packages/{}/{}", self.base_url, name, version);

        let response = self.client
            .get(&url)
            .send()
            .map_err(|e| format!("Failed to fetch package metadata: {}", e))?;

        let status = response.status();
        if !status.is_success() {
            let error_text = response.text().unwrap_or_default();
            return Err(format!(
                "Registry returned error: {} (status {})",
                error_text,
                status
            ));
        }

        response
            .json()
            .map_err(|e| format!("Failed to parse package metadata: {}", e))
    }

    /// Download a package tarball and verify its checksum.
    pub fn download_package(
        &self,
        metadata: &PackageMetadata,
        dest_path: &Path,
    ) -> Result<(), String> {
        // Download tarball
        let response = self.client
            .get(&metadata.tarball_url)
            .send()
            .map_err(|e| format!("Failed to download package: {}", e))?;

        if !response.status().is_success() {
            return Err(format!(
                "Failed to download package: status {}",
                response.status()
            ));
        }

        let tarball_bytes = response
            .bytes()
            .map_err(|e| format!("Failed to read tarball bytes: {}", e))?;

        // Verify checksum
        let mut hasher = Sha256::new();
        hasher.update(&tarball_bytes);
        let computed_checksum = format!("{:x}", hasher.finalize());

        if computed_checksum != metadata.checksum {
            return Err(format!(
                "Checksum mismatch: expected {}, got {}",
                metadata.checksum, computed_checksum
            ));
        }

        // Write tarball to dest_path
        let mut file = std::fs::File::create(dest_path)
            .map_err(|e| format!("Failed to create tarball file: {}", e))?;
        file.write_all(&tarball_bytes)
            .map_err(|e| format!("Failed to write tarball: {}", e))?;

        Ok(())
    }

    /// Extract a tarball to a destination directory.
    pub fn extract_tarball(tarball_path: &Path, dest_dir: &Path) -> Result<(), String> {
        let tarball_file = std::fs::File::open(tarball_path)
            .map_err(|e| format!("Failed to open tarball: {}", e))?;

        let mut archive = tar::Archive::new(tarball_file);

        archive
            .unpack(dest_dir)
            .map_err(|e| format!("Failed to extract tarball: {}", e))?;

        Ok(())
    }
}

impl Default for RegistryClient {
    fn default() -> Self {
        Self::new("https://registry.eclexia.dev".to_string())
    }
}
