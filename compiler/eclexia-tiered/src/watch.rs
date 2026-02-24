// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Watch mode for incremental compilation.
//!
//! Monitors project files for changes and triggers incremental
//! recompilation through the salsa database. File changes are
//! debounced to avoid unnecessary rebuilds during rapid editing.
//!
//! ## Usage
//!
//! ```text
//! eclexia watch              # Watch + type check
//! eclexia watch --run        # Watch + run on change
//! eclexia watch --test       # Watch + run tests on change
//! ```

use std::path::{Path, PathBuf};
use std::time::Duration;

/// Watch mode configuration.
#[derive(Debug, Clone)]
pub struct WatchConfig {
    /// Root directory to watch.
    pub root: PathBuf,
    /// File extensions to watch (e.g., ["ecl", "ecli"]).
    pub extensions: Vec<String>,
    /// Debounce duration (how long to wait after last change).
    pub debounce: Duration,
    /// Action to perform on change.
    pub action: WatchAction,
    /// Directories to ignore.
    pub ignore_dirs: Vec<String>,
}

/// Action to perform when files change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WatchAction {
    /// Type-check only.
    Check,
    /// Build the project.
    Build,
    /// Build and run.
    Run,
    /// Build and run tests.
    Test,
}

impl WatchConfig {
    /// Create a default watch configuration for a project root.
    pub fn new(root: PathBuf) -> Self {
        Self {
            root,
            extensions: vec!["ecl".to_string(), "ecli".to_string()],
            debounce: Duration::from_millis(100),
            action: WatchAction::Check,
            ignore_dirs: vec![
                "target".to_string(),
                ".git".to_string(),
                "node_modules".to_string(),
            ],
        }
    }

    /// Set the watch action.
    pub fn with_action(mut self, action: WatchAction) -> Self {
        self.action = action;
        self
    }

    /// Set the debounce duration.
    pub fn with_debounce(mut self, debounce: Duration) -> Self {
        self.debounce = debounce;
        self
    }

    /// Check if a file should be watched.
    pub fn should_watch(&self, path: &Path) -> bool {
        // Check extension
        let ext_match = path
            .extension()
            .and_then(|e| e.to_str())
            .map(|e| self.extensions.iter().any(|watched| watched == e))
            .unwrap_or(false);

        if !ext_match {
            return false;
        }

        // Check ignored directories
        for component in path.components() {
            if let std::path::Component::Normal(name) = component {
                if let Some(name_str) = name.to_str() {
                    if self.ignore_dirs.iter().any(|ignored| ignored == name_str) {
                        return false;
                    }
                }
            }
        }

        true
    }
}

impl std::fmt::Display for WatchAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Check => write!(f, "check"),
            Self::Build => write!(f, "build"),
            Self::Run => write!(f, "run"),
            Self::Test => write!(f, "test"),
        }
    }
}

/// A file change event.
#[derive(Debug, Clone)]
pub struct FileChange {
    /// Path to the changed file.
    pub path: PathBuf,
    /// Kind of change.
    pub kind: ChangeKind,
}

/// Kind of file change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChangeKind {
    /// File was created or modified.
    Modified,
    /// File was deleted.
    Removed,
}

/// Batch of debounced file changes.
#[derive(Debug, Clone)]
pub struct ChangeBatch {
    /// All changes in this batch.
    pub changes: Vec<FileChange>,
}

impl ChangeBatch {
    /// Create an empty batch.
    pub fn new() -> Self {
        Self {
            changes: Vec::new(),
        }
    }

    /// Add a change to the batch.
    pub fn push(&mut self, change: FileChange) {
        // Deduplicate: if we already have a change for this path, replace it
        if let Some(existing) = self.changes.iter_mut().find(|c| c.path == change.path) {
            existing.kind = change.kind;
        } else {
            self.changes.push(change);
        }
    }

    /// Number of changed files.
    pub fn len(&self) -> usize {
        self.changes.len()
    }

    /// Whether the batch is empty.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
    }

    /// Get all modified files.
    pub fn modified_files(&self) -> Vec<&Path> {
        self.changes
            .iter()
            .filter(|c| c.kind == ChangeKind::Modified)
            .map(|c| c.path.as_path())
            .collect()
    }

    /// Get all removed files.
    pub fn removed_files(&self) -> Vec<&Path> {
        self.changes
            .iter()
            .filter(|c| c.kind == ChangeKind::Removed)
            .map(|c| c.path.as_path())
            .collect()
    }
}

impl Default for ChangeBatch {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_watch_config_default() {
        let config = WatchConfig::new(PathBuf::from("/project"));
        assert_eq!(config.action, WatchAction::Check);
        assert_eq!(config.debounce, Duration::from_millis(100));
        assert_eq!(config.extensions, vec!["ecl", "ecli"]);
    }

    #[test]
    fn test_should_watch_ecl_files() {
        let config = WatchConfig::new(PathBuf::from("/project"));

        assert!(config.should_watch(Path::new("src/main.ecl")));
        assert!(config.should_watch(Path::new("lib/types.ecli")));
        assert!(!config.should_watch(Path::new("src/main.rs")));
        assert!(!config.should_watch(Path::new("README.md")));
    }

    #[test]
    fn test_should_watch_ignores_dirs() {
        let config = WatchConfig::new(PathBuf::from("/project"));

        assert!(!config.should_watch(Path::new("target/debug/main.ecl")));
        assert!(!config.should_watch(Path::new(".git/hooks/main.ecl")));
        assert!(config.should_watch(Path::new("src/main.ecl")));
    }

    #[test]
    fn test_watch_action_display() {
        assert_eq!(format!("{}", WatchAction::Check), "check");
        assert_eq!(format!("{}", WatchAction::Run), "run");
        assert_eq!(format!("{}", WatchAction::Test), "test");
    }

    #[test]
    fn test_change_batch_dedup() {
        let mut batch = ChangeBatch::new();
        batch.push(FileChange {
            path: PathBuf::from("src/main.ecl"),
            kind: ChangeKind::Modified,
        });
        batch.push(FileChange {
            path: PathBuf::from("src/main.ecl"),
            kind: ChangeKind::Modified,
        });

        assert_eq!(batch.len(), 1);
    }

    #[test]
    fn test_change_batch_modified_and_removed() {
        let mut batch = ChangeBatch::new();
        batch.push(FileChange {
            path: PathBuf::from("src/main.ecl"),
            kind: ChangeKind::Modified,
        });
        batch.push(FileChange {
            path: PathBuf::from("src/old.ecl"),
            kind: ChangeKind::Removed,
        });

        assert_eq!(batch.modified_files().len(), 1);
        assert_eq!(batch.removed_files().len(), 1);
    }

    #[test]
    fn test_change_batch_overwrite() {
        let mut batch = ChangeBatch::new();
        batch.push(FileChange {
            path: PathBuf::from("src/main.ecl"),
            kind: ChangeKind::Modified,
        });
        batch.push(FileChange {
            path: PathBuf::from("src/main.ecl"),
            kind: ChangeKind::Removed,
        });

        assert_eq!(batch.len(), 1);
        assert_eq!(batch.changes[0].kind, ChangeKind::Removed);
    }

    #[test]
    fn test_with_action() {
        let config = WatchConfig::new(PathBuf::from("/project")).with_action(WatchAction::Test);
        assert_eq!(config.action, WatchAction::Test);
    }

    #[test]
    fn test_with_debounce() {
        let config =
            WatchConfig::new(PathBuf::from("/project")).with_debounce(Duration::from_millis(500));
        assert_eq!(config.debounce, Duration::from_millis(500));
    }
}
