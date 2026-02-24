// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interop bridge configuration parser and validator.
//!
//! This module reads and validates bridge configuration TOML files
//! for interoperability with other languages (WokeLang, Phronesis, BetLang, AffineScript).

use serde::Deserialize;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct BridgeConfig {
    pub language: LanguageInfo,
    pub existing_ffi: Option<ExistingFFI>,
    pub eclexia_exports: EclexiaExports,
    pub bridge: BridgeInfo,
    pub use_cases: UseCases,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LanguageInfo {
    pub name: String,
    pub repo: String,
    pub build_system: String,
    pub ffi_mechanism: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ExistingFFI {
    pub c_api: Option<String>,
    pub zig_bridge: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct EclexiaExports {
    #[serde(default)]
    pub resource_tracker: bool,
    #[serde(default)]
    pub shadow_prices: bool,
    #[serde(default)]
    pub adaptive_engine: bool,
    #[serde(default)]
    pub carbon_monitor: bool,
    #[serde(default)]
    pub profiler: bool,
    #[serde(default)]
    pub scheduler: bool,
}

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct BridgeInfo {
    pub target_file: Option<String>,
    pub header: Option<String>,
    pub nif_so: Option<String>,
    pub nif_c_src: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct UseCases {
    pub description: String,
}

#[derive(Debug, Clone)]
pub struct BridgeValidation {
    pub bridge_name: String,
    pub valid: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl BridgeConfig {
    /// Load a bridge configuration from a TOML file
    pub fn load(path: &Path) -> Result<Self, String> {
        let contents = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

        toml::from_str(&contents).map_err(|e| format!("Failed to parse {}: {}", path.display(), e))
    }

    /// Validate this bridge configuration
    pub fn validate(&self, project_root: &Path) -> BridgeValidation {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();

        // Check FFI header exists (if specified)
        if let Some(ref header) = self.bridge.header {
            let header_path = project_root.join(header);
            if !header_path.exists() {
                errors.push(format!(
                    "FFI header not found: {} (expected at {})",
                    header,
                    header_path.display()
                ));
            }
        }

        // Check existing FFI paths if specified
        if let Some(ref existing_ffi) = self.existing_ffi {
            if let Some(ref c_api) = existing_ffi.c_api {
                let c_api_path = PathBuf::from(c_api);
                if c_api_path.is_relative() {
                    warnings.push(format!(
                        "C API path is relative: {} (cannot verify without target repo)",
                        c_api
                    ));
                }
            }

            if let Some(ref zig_bridge) = existing_ffi.zig_bridge {
                let zig_path = project_root.join(zig_bridge);
                if !zig_path.exists() {
                    warnings.push(format!(
                        "Zig bridge directory not found: {} (at {})",
                        zig_bridge,
                        zig_path.display()
                    ));
                }
            }
        }

        // Check at least one Eclexia export is enabled
        let exports_enabled = self.eclexia_exports.resource_tracker
            || self.eclexia_exports.shadow_prices
            || self.eclexia_exports.adaptive_engine
            || self.eclexia_exports.carbon_monitor
            || self.eclexia_exports.profiler
            || self.eclexia_exports.scheduler;

        if !exports_enabled {
            warnings
                .push("No Eclexia exports enabled - bridge will have no functionality".to_string());
        }

        BridgeValidation {
            bridge_name: self.language.name.clone(),
            valid: errors.is_empty(),
            errors,
            warnings,
        }
    }
}

/// Load all bridge configurations from the interop directory
pub fn load_all_bridges(interop_dir: &Path) -> Result<HashMap<String, BridgeConfig>, String> {
    let mut bridges = HashMap::new();

    if !interop_dir.exists() {
        return Err(format!(
            "Interop directory not found: {}",
            interop_dir.display()
        ));
    }

    for entry in
        fs::read_dir(interop_dir).map_err(|e| format!("Failed to read interop directory: {}", e))?
    {
        let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;
        let path = entry.path();

        if path.extension().and_then(|s| s.to_str()) == Some("toml") {
            let bridge = BridgeConfig::load(&path)?;
            let name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_string();
            bridges.insert(name, bridge);
        }
    }

    Ok(bridges)
}

/// Validate all bridges and return a summary
pub fn validate_all_bridges(
    interop_dir: &Path,
    project_root: &Path,
) -> Result<Vec<BridgeValidation>, String> {
    let bridges = load_all_bridges(interop_dir)?;
    let mut validations = Vec::new();

    for (_name, bridge) in bridges {
        validations.push(bridge.validate(project_root));
    }

    Ok(validations)
}
