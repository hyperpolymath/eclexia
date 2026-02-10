// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Parallel compilation coordinator.
//!
//! Uses the dependency graph to schedule compilation of independent
//! modules concurrently via rayon. Modules at the same dependency
//! level (with all dependencies already compiled) are compiled in
//! parallel.

use rayon::prelude::*;

use crate::dep_graph::DependencyGraph;
use crate::interface::ModuleInterface;
use crate::ModuleId;

/// Result of compiling a single module.
#[derive(Debug)]
pub struct CompilationUnit {
    /// Module that was compiled.
    pub module_id: ModuleId,
    /// The module's public interface.
    pub interface: ModuleInterface,
    /// Any errors encountered during compilation.
    pub errors: Vec<CompilationError>,
}

/// An error encountered during compilation.
#[derive(Debug, Clone)]
pub struct CompilationError {
    /// Module where the error occurred.
    pub module_id: ModuleId,
    /// Error message.
    pub message: String,
    /// Error severity.
    pub severity: ErrorSeverity,
}

/// Error severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorSeverity {
    Warning,
    Error,
}

/// Parallel compilation scheduler.
///
/// Takes a dependency graph and compiles modules level by level,
/// where each level is processed in parallel.
pub struct ParallelScheduler {
    /// Maximum number of threads to use (0 = rayon default).
    max_threads: usize,
}

impl ParallelScheduler {
    /// Create a new parallel scheduler with default settings.
    pub fn new() -> Self {
        Self { max_threads: 0 }
    }

    /// Set the maximum number of threads.
    pub fn with_max_threads(mut self, threads: usize) -> Self {
        self.max_threads = threads;
        self
    }

    /// Compile all modules in the dependency graph in parallel.
    ///
    /// The `compile_fn` is called for each module and must be thread-safe.
    /// Modules are compiled level by level: all modules in a level have
    /// their dependencies already compiled.
    ///
    /// Returns results in compilation order (leaf modules first).
    pub fn compile_all<F>(
        &self,
        graph: &DependencyGraph,
        compile_fn: F,
    ) -> Result<Vec<CompilationUnit>, ParallelCompilationError>
    where
        F: Fn(&ModuleId) -> CompilationUnit + Sync,
    {
        let levels = graph
            .parallel_levels()
            .ok_or(ParallelCompilationError::CyclicDependency)?;

        tracing::info!(
            "Compiling {} modules in {} levels",
            graph.len(),
            levels.len()
        );

        let pool = if self.max_threads > 0 {
            Some(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(self.max_threads)
                    .build()
                    .map_err(|e| ParallelCompilationError::ThreadPoolError(e.to_string()))?,
            )
        } else {
            None
        };

        let mut all_results = Vec::with_capacity(graph.len());

        for (level_idx, level) in levels.iter().enumerate() {
            tracing::debug!(
                "Level {}: compiling {} modules in parallel",
                level_idx,
                level.len()
            );

            let level_results: Vec<CompilationUnit> = if let Some(ref pool) = pool {
                pool.install(|| {
                    level
                        .par_iter()
                        .map(|module_id| compile_fn(module_id))
                        .collect()
                })
            } else {
                level
                    .par_iter()
                    .map(|module_id| compile_fn(module_id))
                    .collect()
            };

            // Check for fatal errors before proceeding to next level
            let has_errors = level_results.iter().any(|unit| {
                unit.errors
                    .iter()
                    .any(|e| e.severity == ErrorSeverity::Error)
            });

            all_results.extend(level_results);

            if has_errors {
                tracing::warn!("Errors found at level {}, stopping compilation", level_idx);
                return Err(ParallelCompilationError::CompilationFailed {
                    results: all_results,
                });
            }
        }

        Ok(all_results)
    }

    /// Compile only the modules affected by changes to the given modules.
    ///
    /// Uses reverse dependencies to determine the minimal set of modules
    /// that need recompilation.
    pub fn compile_incremental<F>(
        &self,
        graph: &DependencyGraph,
        changed: &[ModuleId],
        compile_fn: F,
    ) -> Result<Vec<CompilationUnit>, ParallelCompilationError>
    where
        F: Fn(&ModuleId) -> CompilationUnit + Sync,
    {
        // Collect all modules that need recompilation
        let mut to_recompile = rustc_hash::FxHashSet::default();

        for module_id in changed {
            to_recompile.insert(module_id.clone());
            for dep in graph.transitive_reverse_dependencies(module_id) {
                to_recompile.insert(dep.clone());
            }
        }

        tracing::info!(
            "{} changed modules, {} total to recompile",
            changed.len(),
            to_recompile.len()
        );

        // Build a subgraph of only the modules that need recompilation
        let mut subgraph = DependencyGraph::new();
        for module_id in &to_recompile {
            subgraph.add_module(module_id.clone());
        }

        // Add edges only between modules in the recompilation set
        for module_id in &to_recompile {
            for dep in graph.dependencies(module_id) {
                if to_recompile.contains(dep) {
                    subgraph.add_dependency(module_id, dep);
                }
            }
        }

        self.compile_all(&subgraph, compile_fn)
    }
}

impl Default for ParallelScheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// Errors during parallel compilation.
#[derive(Debug)]
pub enum ParallelCompilationError {
    /// Dependency graph contains cycles.
    CyclicDependency,
    /// Failed to create thread pool.
    ThreadPoolError(String),
    /// Compilation failed with errors.
    CompilationFailed {
        /// Results collected so far (including errors).
        results: Vec<CompilationUnit>,
    },
}

impl std::fmt::Display for ParallelCompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CyclicDependency => write!(f, "dependency graph contains cycles"),
            Self::ThreadPoolError(msg) => write!(f, "failed to create thread pool: {msg}"),
            Self::CompilationFailed { results } => {
                let error_count: usize = results
                    .iter()
                    .map(|r| {
                        r.errors
                            .iter()
                            .filter(|e| e.severity == ErrorSeverity::Error)
                            .count()
                    })
                    .sum();
                write!(f, "compilation failed with {error_count} errors")
            }
        }
    }
}

impl std::error::Error for ParallelCompilationError {}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hash::FxHashMap;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    fn id(s: &str) -> ModuleId {
        ModuleId::new(s)
    }

    fn dummy_compile(module_id: &ModuleId) -> CompilationUnit {
        CompilationUnit {
            module_id: module_id.clone(),
            interface: ModuleInterface::new(module_id),
            errors: Vec::new(),
        }
    }

    #[test]
    fn test_parallel_compile_linear_chain() {
        // c → b → a (c depends on b, b depends on a)
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("c"), &id("b"));
        graph.add_dependency(&id("b"), &id("a"));

        let scheduler = ParallelScheduler::new();
        let results = scheduler.compile_all(&graph, dummy_compile).unwrap();

        assert_eq!(results.len(), 3);

        // a must be compiled before b, b before c
        let positions: FxHashMap<_, _> = results
            .iter()
            .enumerate()
            .map(|(i, r)| (r.module_id.path.as_str().to_string(), i))
            .collect();

        assert!(positions["a"] < positions["b"]);
        assert!(positions["b"] < positions["c"]);
    }

    #[test]
    fn test_parallel_compile_diamond() {
        // d depends on b and c; b and c depend on a
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("d"), &id("b"));
        graph.add_dependency(&id("d"), &id("c"));
        graph.add_dependency(&id("b"), &id("a"));
        graph.add_dependency(&id("c"), &id("a"));

        let compile_counter = Arc::new(AtomicUsize::new(0));
        let counter = compile_counter.clone();

        let scheduler = ParallelScheduler::new();
        let results = scheduler
            .compile_all(&graph, |module_id| {
                counter.fetch_add(1, Ordering::Relaxed);
                dummy_compile(module_id)
            })
            .unwrap();

        assert_eq!(results.len(), 4);
        assert_eq!(compile_counter.load(Ordering::Relaxed), 4);
    }

    #[test]
    fn test_parallel_compile_independent() {
        // Three independent modules — all at level 0
        let mut graph = DependencyGraph::new();
        graph.add_module(id("x"));
        graph.add_module(id("y"));
        graph.add_module(id("z"));

        let scheduler = ParallelScheduler::new();
        let results = scheduler.compile_all(&graph, dummy_compile).unwrap();

        assert_eq!(results.len(), 3);
    }

    #[test]
    fn test_parallel_compile_with_errors() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("b"), &id("a"));

        let scheduler = ParallelScheduler::new();
        let result = scheduler.compile_all(&graph, |module_id| {
            let mut unit = dummy_compile(module_id);
            if module_id.path.as_str() == "a" {
                unit.errors.push(CompilationError {
                    module_id: module_id.clone(),
                    message: "type error".to_string(),
                    severity: ErrorSeverity::Error,
                });
            }
            unit
        });

        assert!(result.is_err());
        if let Err(ParallelCompilationError::CompilationFailed { results }) = result {
            // a was compiled (level 0) but b was not (level 1 skipped)
            assert_eq!(results.len(), 1);
        }
    }

    #[test]
    fn test_parallel_compile_cycle_detection() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("a"), &id("b"));
        graph.add_dependency(&id("b"), &id("a"));

        let scheduler = ParallelScheduler::new();
        let result = scheduler.compile_all(&graph, dummy_compile);

        assert!(matches!(
            result,
            Err(ParallelCompilationError::CyclicDependency)
        ));
    }

    #[test]
    fn test_incremental_compile() {
        // d → b → a, d → c → a
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("d"), &id("b"));
        graph.add_dependency(&id("d"), &id("c"));
        graph.add_dependency(&id("b"), &id("a"));
        graph.add_dependency(&id("c"), &id("a"));

        let compile_counter = Arc::new(AtomicUsize::new(0));
        let counter = compile_counter.clone();

        let scheduler = ParallelScheduler::new();

        // Only "a" changed — must recompile a, b, c, d (all depend on a)
        let results = scheduler
            .compile_incremental(&graph, &[id("a")], |module_id| {
                counter.fetch_add(1, Ordering::Relaxed);
                dummy_compile(module_id)
            })
            .unwrap();

        assert_eq!(results.len(), 4);
        assert_eq!(compile_counter.load(Ordering::Relaxed), 4);
    }

    #[test]
    fn test_incremental_compile_leaf_change() {
        // d → b → a, d → c → a
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("d"), &id("b"));
        graph.add_dependency(&id("d"), &id("c"));
        graph.add_dependency(&id("b"), &id("a"));
        graph.add_dependency(&id("c"), &id("a"));

        let compile_counter = Arc::new(AtomicUsize::new(0));
        let counter = compile_counter.clone();

        let scheduler = ParallelScheduler::new();

        // Only "d" changed — only recompile d (nothing depends on d)
        let results = scheduler
            .compile_incremental(&graph, &[id("d")], |module_id| {
                counter.fetch_add(1, Ordering::Relaxed);
                dummy_compile(module_id)
            })
            .unwrap();

        assert_eq!(results.len(), 1);
        assert_eq!(compile_counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_custom_thread_count() {
        let mut graph = DependencyGraph::new();
        graph.add_module(id("a"));
        graph.add_module(id("b"));

        let scheduler = ParallelScheduler::new().with_max_threads(2);
        let results = scheduler.compile_all(&graph, dummy_compile).unwrap();

        assert_eq!(results.len(), 2);
    }
}
