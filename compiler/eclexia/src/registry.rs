// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! HTTP registry client for package downloads.

use flate2::read::GzDecoder;
use reqwest::blocking::Client;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

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

        let response = self
            .client
            .get(&url)
            .send()
            .map_err(|e| format!("Failed to fetch package metadata: {}", e))?;

        let status = response.status();
        if !status.is_success() {
            let error_text = response.text().unwrap_or_default();
            return Err(format!(
                "Registry returned error: {} (status {})",
                error_text, status
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
        let response = self
            .client
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
        let mut tarball_file = std::fs::File::open(tarball_path)
            .map_err(|e| format!("Failed to open tarball: {}", e))?;

        // Detect gzip-compressed tarballs by magic bytes so both .tar and .tar.gz work.
        let mut magic = [0u8; 2];
        let is_gzip = tarball_file.read_exact(&mut magic).is_ok() && magic == [0x1f, 0x8b];
        tarball_file
            .seek(SeekFrom::Start(0))
            .map_err(|e| format!("Failed to rewind tarball file: {}", e))?;

        if is_gzip {
            let decoder = GzDecoder::new(tarball_file);
            let mut archive = tar::Archive::new(decoder);
            archive
                .unpack(dest_dir)
                .map_err(|e| format!("Failed to extract tarball: {}", e))?;
        } else {
            let mut archive = tar::Archive::new(tarball_file);
            archive
                .unpack(dest_dir)
                .map_err(|e| format!("Failed to extract tarball: {}", e))?;
        }

        Ok(())
    }
}

impl Default for RegistryClient {
    fn default() -> Self {
        Self::new("https://registry.eclexia.dev".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::RegistryClient;
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_temp_path(prefix: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        p.push(format!("{}_{}_{}", prefix, std::process::id(), ts));
        p
    }

    fn append_test_entry<W: std::io::Write>(
        builder: &mut tar::Builder<W>,
        rel_path: &str,
        bytes: &[u8],
    ) -> Result<(), String> {
        let mut header = tar::Header::new_gnu();
        header
            .set_path(rel_path)
            .map_err(|e| format!("set_path failed: {}", e))?;
        header.set_size(bytes.len() as u64);
        header.set_mode(0o644);
        header.set_cksum();
        builder
            .append(&header, bytes)
            .map_err(|e| format!("append failed: {}", e))
    }

    fn write_test_tarball(path: &Path, gzip: bool) -> Result<(), String> {
        let payload = b"hello from eclexia registry test";
        if gzip {
            let file = std::fs::File::create(path)
                .map_err(|e| format!("create gz tarball failed: {}", e))?;
            let encoder = GzEncoder::new(file, Compression::default());
            let mut builder = tar::Builder::new(encoder);
            append_test_entry(&mut builder, "pkg/data.txt", payload)?;
            builder
                .finish()
                .map_err(|e| format!("finish gz tarball failed: {}", e))?;
            let encoder = builder
                .into_inner()
                .map_err(|e| format!("finalize gz tarball failed: {}", e))?;
            let _ = encoder
                .finish()
                .map_err(|e| format!("flush gzip stream failed: {}", e))?;
        } else {
            let file = std::fs::File::create(path)
                .map_err(|e| format!("create tarball failed: {}", e))?;
            let mut builder = tar::Builder::new(file);
            append_test_entry(&mut builder, "pkg/data.txt", payload)?;
            builder
                .finish()
                .map_err(|e| format!("finish tarball failed: {}", e))?;
        }
        Ok(())
    }

    #[test]
    fn extract_plain_tarball() {
        let tar_path = unique_temp_path("eclexia_registry_plain").with_extension("tar");
        let out_dir = unique_temp_path("eclexia_registry_plain_out");
        fs::create_dir_all(&out_dir).expect("create output dir");

        write_test_tarball(&tar_path, false).expect("write plain tarball");
        RegistryClient::extract_tarball(&tar_path, &out_dir).expect("extract plain tarball");

        let extracted = out_dir.join("pkg/data.txt");
        let contents = fs::read_to_string(&extracted).expect("read extracted file");
        assert_eq!(contents, "hello from eclexia registry test");

        let _ = fs::remove_file(&tar_path);
        let _ = fs::remove_dir_all(&out_dir);
    }

    #[test]
    fn extract_gzip_tarball() {
        let tar_path = unique_temp_path("eclexia_registry_gz").with_extension("tar.gz");
        let out_dir = unique_temp_path("eclexia_registry_gz_out");
        fs::create_dir_all(&out_dir).expect("create output dir");

        write_test_tarball(&tar_path, true).expect("write gzip tarball");
        RegistryClient::extract_tarball(&tar_path, &out_dir).expect("extract gzip tarball");

        let extracted = out_dir.join("pkg/data.txt");
        let contents = fs::read_to_string(&extracted).expect("read extracted file");
        assert_eq!(contents, "hello from eclexia registry test");

        let _ = fs::remove_file(&tar_path);
        let _ = fs::remove_dir_all(&out_dir);
    }
}
