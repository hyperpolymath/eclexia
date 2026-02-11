// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Package management for Eclexia projects.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Package manifest (package.toml).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageManifest {
    pub package: PackageMetadata,
    #[serde(default)]
    pub dependencies: HashMap<String, String>,
    #[serde(default, rename = "dev-dependencies")]
    pub dev_dependencies: HashMap<String, String>,
    #[serde(default)]
    pub build: BuildConfig,
    #[serde(default)]
    pub resources: ResourceLimits,
    #[serde(default)]
    pub features: Features,
}

/// Package metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageMetadata {
    pub name: String,
    pub version: String,
    pub authors: Vec<String>,
    pub edition: String,
    pub description: Option<String>,
    pub license: Option<String>,
    pub repository: Option<String>,
}

/// Build configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildConfig {
    #[serde(default = "default_output")]
    pub output: OutputType,
    #[serde(default = "default_entry")]
    pub entry: PathBuf,
}

impl Default for BuildConfig {
    fn default() -> Self {
        Self {
            output: OutputType::Bin,
            entry: PathBuf::from("src/main.ecl"),
        }
    }
}

fn default_output() -> OutputType {
    OutputType::Bin
}

fn default_entry() -> PathBuf {
    PathBuf::from("src/main.ecl")
}

/// Output type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OutputType {
    Bin,
    Lib,
}

/// Resource limits.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ResourceLimits {
    pub energy: Option<String>,
    pub time: Option<String>,
    pub memory: Option<String>,
    pub carbon: Option<String>,
}

/// Feature flags.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Features {
    #[serde(default)]
    pub default: Vec<String>,
    #[serde(flatten)]
    pub features: HashMap<String, Vec<String>>,
}

impl Default for Features {
    fn default() -> Self {
        Self {
            default: vec!["std".to_string()],
            features: HashMap::new(),
        }
    }
}

/// Load a package manifest from a directory.
pub fn load_manifest(path: &Path) -> Result<PackageManifest, String> {
    let manifest_path = path.join("package.toml");
    let contents = fs::read_to_string(&manifest_path)
        .map_err(|e| format!("Failed to read package.toml: {}", e))?;

    toml::from_str(&contents).map_err(|e| format!("Failed to parse package.toml: {}", e))
}

/// Create a new package manifest.
pub fn create_manifest(name: String, authors: Vec<String>, output: OutputType) -> PackageManifest {
    PackageManifest {
        package: PackageMetadata {
            name,
            version: "0.1.0".to_string(),
            authors,
            edition: "2025".to_string(),
            description: None,
            license: Some("PMPL-1.0-or-later".to_string()),
            repository: None,
        },
        dependencies: HashMap::new(),
        dev_dependencies: HashMap::new(),
        build: BuildConfig {
            output,
            entry: if output == OutputType::Bin {
                PathBuf::from("src/main.ecl")
            } else {
                PathBuf::from("src/lib.ecl")
            },
        },
        resources: ResourceLimits::default(),
        features: Features::default(),
    }
}

/// Save a package manifest to a directory.
pub fn save_manifest(path: &Path, manifest: &PackageManifest) -> Result<(), String> {
    let manifest_path = path.join("package.toml");
    let contents = toml::to_string_pretty(manifest)
        .map_err(|e| format!("Failed to serialize package.toml: {}", e))?;

    fs::write(&manifest_path, contents).map_err(|e| format!("Failed to write package.toml: {}", e))
}

/// Add a dependency to the manifest.
pub fn add_dependency(manifest: &mut PackageManifest, name: String, version: String, dev: bool) {
    if dev {
        manifest.dev_dependencies.insert(name, version);
    } else {
        manifest.dependencies.insert(name, version);
    }
}

/// Remove a dependency from the manifest.
pub fn remove_dependency(manifest: &mut PackageManifest, name: &str, dev: bool) -> bool {
    if dev {
        manifest.dev_dependencies.remove(name).is_some()
    } else {
        manifest.dependencies.remove(name).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(err) => panic!("Expected Ok, got Err: {:?}", err),
        }
    }

    #[test]
    fn test_parse_manifest() {
        let toml = r#"
[package]
name = "test-package"
version = "0.1.0"
authors = ["Test Author <test@example.com>"]
edition = "2025"

[dependencies]
core = "0.1"

[build]
output = "bin"
entry = "src/main.ecl"
"#;

        let manifest: PackageManifest = expect_ok(toml::from_str(toml));
        assert_eq!(manifest.package.name, "test-package");
        assert_eq!(manifest.package.version, "0.1.0");
        assert_eq!(manifest.dependencies.get("core"), Some(&"0.1".to_string()));
        assert_eq!(manifest.build.output, OutputType::Bin);
    }
}
