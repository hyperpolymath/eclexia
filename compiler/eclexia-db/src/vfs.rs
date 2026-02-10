// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Virtual File System (VFS) for the Eclexia compiler.
//!
//! The VFS provides an in-memory file store that:
//! - Tracks all project source files
//! - Integrates with `notify` for file-system watching
//! - Feeds file changes into the salsa database
//!
//! Both the CLI (for watch mode) and LSP (for document sync)
//! use the VFS as the bridge between the outside world and
//! the incremental compilation database.

use std::path::{Path, PathBuf};

use rustc_hash::FxHashMap;
use salsa::Setter;

use crate::{CompilerDatabase, SourceFile};

/// A change to a file in the VFS.
#[derive(Debug, Clone)]
pub enum FileChange {
    /// A file was added or its content changed.
    Added { path: PathBuf, text: String },
    /// A file's content changed.
    Changed { path: PathBuf, text: String },
    /// A file was removed.
    Removed { path: PathBuf },
}

/// A batch of file changes to apply atomically.
#[derive(Debug, Clone, Default)]
pub struct ChangeSet {
    pub changes: Vec<FileChange>,
}

impl ChangeSet {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a file change to the batch.
    pub fn add(&mut self, change: FileChange) {
        self.changes.push(change);
    }

    /// Create a change set from a single file read.
    pub fn from_file(path: PathBuf, text: String) -> Self {
        Self {
            changes: vec![FileChange::Added { path, text }],
        }
    }
}

/// The Virtual File System.
///
/// Maintains an in-memory map of file paths to their salsa `SourceFile`
/// inputs. When files change, the VFS updates the corresponding salsa
/// inputs, which triggers incremental re-computation of affected queries.
pub struct Vfs {
    /// Map from file path to salsa SourceFile input.
    files: FxHashMap<PathBuf, SourceFile>,
}

impl Vfs {
    /// Create a new empty VFS.
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
        }
    }

    /// Apply a batch of file changes to the database.
    ///
    /// This is the primary way to feed file changes into the
    /// incremental compilation pipeline. After calling this,
    /// any salsa queries that depended on changed files will
    /// be re-executed on next access.
    pub fn apply_changes(&mut self, db: &mut CompilerDatabase, changes: ChangeSet) {
        for change in changes.changes {
            match change {
                FileChange::Added { path, text } | FileChange::Changed { path, text } => {
                    if let Some(source) = self.files.get(&path) {
                        // File already tracked — update its text
                        source.set_text(db).to(text);
                    } else {
                        // New file — create a salsa input
                        let source = SourceFile::new(db, text);
                        self.files.insert(path, source);
                    }
                }
                FileChange::Removed { path } => {
                    self.files.remove(&path);
                }
            }
        }
    }

    /// Get the salsa `SourceFile` for a path, if tracked.
    pub fn get(&self, path: &Path) -> Option<SourceFile> {
        self.files.get(path).copied()
    }

    /// Check if a path is tracked by the VFS.
    pub fn contains(&self, path: &Path) -> bool {
        self.files.contains_key(path)
    }

    /// Get all tracked file paths.
    pub fn files(&self) -> impl Iterator<Item = &PathBuf> {
        self.files.keys()
    }

    /// Get all tracked files as (path, source) pairs.
    pub fn entries(&self) -> impl Iterator<Item = (&PathBuf, &SourceFile)> {
        self.files.iter()
    }

    /// Number of tracked files.
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Whether the VFS is empty.
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Load a file from disk into the VFS.
    pub fn load_file(
        &mut self,
        db: &mut CompilerDatabase,
        path: &Path,
    ) -> std::io::Result<SourceFile> {
        let text = std::fs::read_to_string(path)?;
        let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

        let source = SourceFile::new(db, text);
        self.files.insert(canonical, source);
        Ok(source)
    }

    /// Load all `.ecl` files from a directory (recursively).
    pub fn load_directory(
        &mut self,
        db: &mut CompilerDatabase,
        dir: &Path,
    ) -> std::io::Result<Vec<PathBuf>> {
        let mut loaded = Vec::new();
        self.load_directory_recursive(db, dir, &mut loaded)?;
        Ok(loaded)
    }

    fn load_directory_recursive(
        &mut self,
        db: &mut CompilerDatabase,
        dir: &Path,
        loaded: &mut Vec<PathBuf>,
    ) -> std::io::Result<()> {
        if !dir.is_dir() {
            return Ok(());
        }

        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if name.starts_with('.') || name == "target" {
                        continue;
                    }
                }
                self.load_directory_recursive(db, &path, loaded)?;
            } else if path.extension().and_then(|e| e.to_str()) == Some("ecl") {
                self.load_file(db, &path)?;
                loaded.push(path);
            }
        }

        Ok(())
    }
}

impl Default for Vfs {
    fn default() -> Self {
        Self::new()
    }
}

/// File watcher that feeds changes into the VFS.
///
/// Uses the `notify` crate to watch for file-system changes
/// and debounces them before applying to the database.
pub struct FileWatcher {
    /// Debounce duration in milliseconds
    debounce_ms: u64,
}

impl FileWatcher {
    /// Create a new file watcher with the given debounce duration.
    pub fn new(debounce_ms: u64) -> Self {
        Self { debounce_ms }
    }

    /// Start watching a directory for changes.
    ///
    /// Returns a channel receiver that yields `ChangeSet` batches
    /// whenever files change on disk.
    pub fn watch(&self, path: PathBuf) -> std::io::Result<std::sync::mpsc::Receiver<ChangeSet>> {
        use notify::{RecursiveMode, Watcher};
        use std::sync::mpsc;

        let (tx, rx) = mpsc::channel();
        let debounce_ms = self.debounce_ms;

        std::thread::spawn(move || {
            let (notify_tx, notify_rx) = mpsc::channel();

            let mut watcher = match notify::recommended_watcher(
                move |res: Result<notify::Event, notify::Error>| {
                    if let Ok(event) = res {
                        let _ = notify_tx.send(event);
                    }
                },
            ) {
                Ok(w) => w,
                Err(e) => {
                    tracing::error!("Failed to create file watcher: {}", e);
                    return;
                }
            };

            if let Err(e) = watcher.watch(&path, RecursiveMode::Recursive) {
                tracing::error!("Failed to watch path {}: {}", path.display(), e);
                return;
            }

            tracing::info!("Watching {} for changes", path.display());

            loop {
                let Ok(first_event) = notify_rx.recv() else {
                    break;
                };

                let mut events = vec![first_event];

                // Collect more events within debounce window
                let deadline =
                    std::time::Instant::now() + std::time::Duration::from_millis(debounce_ms);

                while std::time::Instant::now() < deadline {
                    match notify_rx
                        .recv_timeout(deadline.saturating_duration_since(std::time::Instant::now()))
                    {
                        Ok(event) => events.push(event),
                        Err(_) => break,
                    }
                }

                let mut changeset = ChangeSet::new();
                let mut seen = rustc_hash::FxHashSet::default();

                for event in events {
                    for path in event.paths {
                        if path.extension().and_then(|e| e.to_str()) != Some("ecl") {
                            continue;
                        }

                        if !seen.insert(path.clone()) {
                            continue;
                        }

                        if path.exists() {
                            if let Ok(text) = std::fs::read_to_string(&path) {
                                changeset.add(FileChange::Changed { path, text });
                            }
                        } else {
                            changeset.add(FileChange::Removed { path });
                        }
                    }
                }

                if !changeset.changes.is_empty() && tx.send(changeset).is_err() {
                    break;
                }
            }
        });

        Ok(rx)
    }
}

impl Default for FileWatcher {
    fn default() -> Self {
        Self::new(100)
    }
}
