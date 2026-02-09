// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Dependency resolution for Eclexia packages.
//!
//! This module implements a dependency resolver that:
//! - Parses semantic version requirements
//! - Builds a dependency graph
//! - Detects version conflicts
//! - Resolves dependencies to concrete versions

use std::collections::{HashMap, HashSet};
use std::cmp::Ordering;
use std::fmt;

/// A semantic version (major.minor.patch).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl Version {
    /// Create a new version.
    pub fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self { major, minor, patch }
    }

    /// Parse a version string (e.g., "1.2.3").
    pub fn parse(s: &str) -> Result<Self, String> {
        let parts: Vec<&str> = s.split('.').collect();
        if parts.len() != 3 {
            return Err(format!("Invalid version format: {}", s));
        }

        let major = parts[0]
            .parse()
            .map_err(|_| format!("Invalid major version: {}", parts[0]))?;
        let minor = parts[1]
            .parse()
            .map_err(|_| format!("Invalid minor version: {}", parts[1]))?;
        let patch = parts[2]
            .parse()
            .map_err(|_| format!("Invalid patch version: {}", parts[2]))?;

        Ok(Self::new(major, minor, patch))
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => match self.minor.cmp(&other.minor) {
                Ordering::Equal => self.patch.cmp(&other.patch),
                other => other,
            },
            other => other,
        }
    }
}

/// A version requirement (e.g., "^1.2.0", ">=1.0.0", "1.2.3").
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VersionReq {
    /// Exact version match (e.g., "1.2.3")
    Exact(Version),
    /// Compatible with (caret: ^1.2.3 means >=1.2.3 <2.0.0)
    Caret(Version),
    /// Greater than or equal to (>=1.2.3)
    GreaterEq(Version),
    /// Less than (<2.0.0)
    Less(Version),
    /// Any version (*)
    Any,
}

impl VersionReq {
    /// Parse a version requirement string.
    pub fn parse(s: &str) -> Result<Self, String> {
        let s = s.trim();

        if s == "*" {
            return Ok(VersionReq::Any);
        }

        if let Some(rest) = s.strip_prefix("^") {
            let version = Version::parse(rest)?;
            return Ok(VersionReq::Caret(version));
        }

        if let Some(rest) = s.strip_prefix(">=") {
            let version = Version::parse(rest)?;
            return Ok(VersionReq::GreaterEq(version));
        }

        if let Some(rest) = s.strip_prefix("<") {
            let version = Version::parse(rest)?;
            return Ok(VersionReq::Less(version));
        }

        // Default: exact version
        let version = Version::parse(s)?;
        Ok(VersionReq::Exact(version))
    }

    /// Check if a version satisfies this requirement.
    pub fn matches(&self, version: &Version) -> bool {
        match self {
            VersionReq::Exact(v) => version == v,
            VersionReq::Caret(v) => {
                // ^1.2.3 means >=1.2.3 <2.0.0
                version >= v && version.major == v.major
            }
            VersionReq::GreaterEq(v) => version >= v,
            VersionReq::Less(v) => version < v,
            VersionReq::Any => true,
        }
    }
}

/// A dependency entry.
#[derive(Debug, Clone)]
pub struct Dependency {
    pub name: String,
    pub version_req: VersionReq,
}

/// A resolved package with its concrete version.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedPackage {
    pub name: String,
    pub version: Version,
}

/// A package in the dependency graph.
#[derive(Debug, Clone)]
struct PackageNode {
    name: String,
    version: Version,
    dependencies: Vec<Dependency>,
}

/// Dependency resolution error.
#[derive(Debug, Clone)]
pub enum ResolutionError {
    /// Version conflict detected
    Conflict {
        package: String,
        required: Vec<String>,
    },
    /// Package not found
    NotFound(String),
    /// Circular dependency detected
    CircularDependency(Vec<String>),
    /// Version requirement not satisfied
    UnsatisfiedRequirement {
        package: String,
        requirement: String,
        available: Vec<Version>,
    },
}

impl fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ResolutionError::Conflict { package, required } => {
                write!(
                    f,
                    "Version conflict for package '{}': required versions {}",
                    package,
                    required.join(", ")
                )
            }
            ResolutionError::NotFound(name) => {
                write!(f, "Package '{}' not found", name)
            }
            ResolutionError::CircularDependency(cycle) => {
                write!(f, "Circular dependency detected: {}", cycle.join(" -> "))
            }
            ResolutionError::UnsatisfiedRequirement {
                package,
                requirement,
                available,
            } => {
                let versions: Vec<String> = available.iter().map(|v| v.to_string()).collect();
                write!(
                    f,
                    "No version of '{}' satisfies requirement '{}'. Available: {}",
                    package,
                    requirement,
                    versions.join(", ")
                )
            }
        }
    }
}

impl std::error::Error for ResolutionError {}

/// A dependency resolver.
pub struct Resolver {
    /// Available packages and their versions
    registry: HashMap<String, Vec<PackageNode>>,
}

impl Resolver {
    /// Create a new resolver.
    pub fn new() -> Self {
        Self {
            registry: HashMap::new(),
        }
    }

    /// Register a package version with its dependencies.
    pub fn register_package(
        &mut self,
        name: String,
        version: Version,
        dependencies: Vec<Dependency>,
    ) {
        let node = PackageNode {
            name: name.clone(),
            version,
            dependencies,
        };

        self.registry
            .entry(name)
            .or_insert_with(Vec::new)
            .push(node);
    }

    /// Resolve dependencies for a package.
    pub fn resolve(
        &self,
        root_dependencies: &[Dependency],
    ) -> Result<Vec<ResolvedPackage>, ResolutionError> {
        let mut resolved = HashMap::new();
        let mut in_progress = HashSet::new();

        for dep in root_dependencies {
            self.resolve_dep(dep, &mut resolved, &mut in_progress, Vec::new())?;
        }

        // Convert to sorted list (topological order)
        let mut result: Vec<_> = resolved.into_values().collect();
        result.sort_by(|a, b| a.name.cmp(&b.name));

        Ok(result)
    }

    /// Resolve a single dependency recursively.
    fn resolve_dep(
        &self,
        dep: &Dependency,
        resolved: &mut HashMap<String, ResolvedPackage>,
        in_progress: &mut HashSet<String>,
        path: Vec<String>,
    ) -> Result<(), ResolutionError> {
        // Check for circular dependency
        if in_progress.contains(&dep.name) {
            let mut cycle = path.clone();
            cycle.push(dep.name.clone());
            return Err(ResolutionError::CircularDependency(cycle));
        }

        // Already resolved?
        if let Some(existing) = resolved.get(&dep.name) {
            // Check if existing version satisfies requirement
            if !dep.version_req.matches(&existing.version) {
                return Err(ResolutionError::Conflict {
                    package: dep.name.clone(),
                    required: vec![format!("{:?}", dep.version_req)],
                });
            }
            return Ok(());
        }

        // Find package versions
        let versions = self
            .registry
            .get(&dep.name)
            .ok_or_else(|| ResolutionError::NotFound(dep.name.clone()))?;

        // Find the highest version that satisfies the requirement
        let package = versions
            .iter()
            .filter(|p| dep.version_req.matches(&p.version))
            .max_by_key(|p| p.version)
            .ok_or_else(|| ResolutionError::UnsatisfiedRequirement {
                package: dep.name.clone(),
                requirement: format!("{:?}", dep.version_req),
                available: versions.iter().map(|p| p.version).collect(),
            })?;

        // Mark as in-progress
        in_progress.insert(dep.name.clone());

        // Resolve dependencies
        let mut new_path = path;
        new_path.push(dep.name.clone());

        for sub_dep in &package.dependencies {
            self.resolve_dep(sub_dep, resolved, in_progress, new_path.clone())?;
        }

        // Mark as resolved
        in_progress.remove(&dep.name);
        resolved.insert(
            dep.name.clone(),
            ResolvedPackage {
                name: dep.name.clone(),
                version: package.version,
            },
        );

        Ok(())
    }
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Simplified dependency resolution for package manager.
/// Takes a HashMap of name -> version requirement and returns resolved packages.
/// Note: This is a simplified version that doesn't query a real registry yet.
/// For now, it just parses the dependency declarations and returns them as-is.
pub fn resolve_dependencies(
    dependencies: &HashMap<String, String>,
) -> Result<Vec<(String, String)>, String> {
    // For now, just return the dependencies as specified
    // TODO: Implement full resolution with registry queries
    let resolved: Vec<(String, String)> = dependencies
        .iter()
        .map(|(name, version)| (name.clone(), version.clone()))
        .collect();

    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_parse() {
        let v = Version::parse("1.2.3").unwrap();
        assert_eq!(v.major, 1);
        assert_eq!(v.minor, 2);
        assert_eq!(v.patch, 3);
    }

    #[test]
    fn test_version_compare() {
        let v1 = Version::new(1, 2, 3);
        let v2 = Version::new(1, 2, 4);
        let v3 = Version::new(2, 0, 0);

        assert!(v1 < v2);
        assert!(v2 < v3);
        assert!(v1 < v3);
    }

    #[test]
    fn test_version_req_exact() {
        let req = VersionReq::parse("1.2.3").unwrap();
        assert!(req.matches(&Version::new(1, 2, 3)));
        assert!(!req.matches(&Version::new(1, 2, 4)));
    }

    #[test]
    fn test_version_req_caret() {
        let req = VersionReq::parse("^1.2.3").unwrap();
        assert!(req.matches(&Version::new(1, 2, 3)));
        assert!(req.matches(&Version::new(1, 3, 0)));
        assert!(!req.matches(&Version::new(2, 0, 0)));
    }

    #[test]
    fn test_simple_resolution() {
        let mut resolver = Resolver::new();

        // Register packages
        resolver.register_package("foo".to_string(), Version::new(1, 0, 0), vec![]);
        resolver.register_package(
            "bar".to_string(),
            Version::new(1, 0, 0),
            vec![Dependency {
                name: "foo".to_string(),
                version_req: VersionReq::parse("^1.0.0").unwrap(),
            }],
        );

        // Resolve
        let deps = vec![Dependency {
            name: "bar".to_string(),
            version_req: VersionReq::parse("^1.0.0").unwrap(),
        }];

        let resolved = resolver.resolve(&deps).unwrap();
        assert_eq!(resolved.len(), 2);
        assert!(resolved.iter().any(|p| p.name == "foo"));
        assert!(resolved.iter().any(|p| p.name == "bar"));
    }

    #[test]
    fn test_version_selection() {
        let mut resolver = Resolver::new();

        // Register multiple versions
        resolver.register_package("foo".to_string(), Version::new(1, 0, 0), vec![]);
        resolver.register_package("foo".to_string(), Version::new(1, 1, 0), vec![]);
        resolver.register_package("foo".to_string(), Version::new(2, 0, 0), vec![]);

        // Resolve with caret requirement
        let deps = vec![Dependency {
            name: "foo".to_string(),
            version_req: VersionReq::parse("^1.0.0").unwrap(),
        }];

        let resolved = resolver.resolve(&deps).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0].version, Version::new(1, 1, 0)); // Highest 1.x version
    }

    #[test]
    fn test_circular_dependency() {
        let mut resolver = Resolver::new();

        // foo -> bar -> foo (circular)
        resolver.register_package(
            "foo".to_string(),
            Version::new(1, 0, 0),
            vec![Dependency {
                name: "bar".to_string(),
                version_req: VersionReq::parse("^1.0.0").unwrap(),
            }],
        );
        resolver.register_package(
            "bar".to_string(),
            Version::new(1, 0, 0),
            vec![Dependency {
                name: "foo".to_string(),
                version_req: VersionReq::parse("^1.0.0").unwrap(),
            }],
        );

        let deps = vec![Dependency {
            name: "foo".to_string(),
            version_req: VersionReq::parse("^1.0.0").unwrap(),
        }];

        let result = resolver.resolve(&deps);
        assert!(matches!(result, Err(ResolutionError::CircularDependency(_))));
    }
}
