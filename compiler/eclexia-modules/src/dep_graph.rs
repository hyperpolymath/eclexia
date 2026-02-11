// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Module dependency graph for compilation scheduling.
//!
//! The dependency graph tracks which modules depend on which others,
//! enabling:
//! - Topological ordering for sequential compilation
//! - Parallel compilation of independent modules at the same level
//! - Reverse dependency lookup for incremental recompilation
//! - Cycle detection to report circular imports

use petgraph::algo;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::Direction;
use rustc_hash::FxHashMap;

use crate::ModuleId;

/// A directed graph of module dependencies.
///
/// An edge from A → B means "A depends on B" (A imports B).
/// Compilation must process B before A.
pub struct DependencyGraph {
    /// The underlying directed graph.
    graph: DiGraph<ModuleId, ()>,
    /// Map from module ID to graph node index.
    nodes: FxHashMap<ModuleId, NodeIndex>,
}

impl DependencyGraph {
    /// Create a new empty dependency graph.
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            nodes: FxHashMap::default(),
        }
    }

    /// Add a module to the graph (if not already present).
    pub fn add_module(&mut self, module_id: ModuleId) -> NodeIndex {
        if let Some(&idx) = self.nodes.get(&module_id) {
            return idx;
        }
        let idx = self.graph.add_node(module_id.clone());
        self.nodes.insert(module_id, idx);
        idx
    }

    /// Add a dependency edge: `from` depends on `to`.
    ///
    /// Both modules must already be added to the graph.
    pub fn add_dependency(&mut self, from: &ModuleId, to: &ModuleId) {
        let from_idx = self.add_module(from.clone());
        let to_idx = self.add_module(to.clone());
        self.graph.add_edge(from_idx, to_idx, ());
    }

    /// Get all direct dependencies of a module.
    pub fn dependencies(&self, module_id: &ModuleId) -> Vec<&ModuleId> {
        let Some(&idx) = self.nodes.get(module_id) else {
            return vec![];
        };
        self.graph
            .neighbors_directed(idx, Direction::Outgoing)
            .map(|n| &self.graph[n])
            .collect()
    }

    /// Get all direct dependents (reverse dependencies) of a module.
    ///
    /// These are the modules that would need recompilation if the
    /// given module changes.
    pub fn reverse_dependencies(&self, module_id: &ModuleId) -> Vec<&ModuleId> {
        let Some(&idx) = self.nodes.get(module_id) else {
            return vec![];
        };
        self.graph
            .neighbors_directed(idx, Direction::Incoming)
            .map(|n| &self.graph[n])
            .collect()
    }

    /// Get all transitive dependents of a module.
    ///
    /// This is the full set of modules that need recompilation
    /// when the given module changes.
    pub fn transitive_reverse_dependencies(&self, module_id: &ModuleId) -> Vec<&ModuleId> {
        let Some(&idx) = self.nodes.get(module_id) else {
            return vec![];
        };

        let mut visited = rustc_hash::FxHashSet::default();
        let mut stack = vec![idx];
        let mut result = Vec::new();

        while let Some(node) = stack.pop() {
            for neighbor in self.graph.neighbors_directed(node, Direction::Incoming) {
                if visited.insert(neighbor) {
                    result.push(&self.graph[neighbor]);
                    stack.push(neighbor);
                }
            }
        }

        result
    }

    /// Compute a topological ordering of all modules.
    ///
    /// Returns modules in compilation order: leaf modules (no dependencies)
    /// first, then modules that depend only on already-compiled modules.
    ///
    /// Returns `None` if there is a cycle.
    pub fn topological_order(&self) -> Option<Vec<&ModuleId>> {
        algo::toposort(&self.graph, None).ok().map(|sorted| {
            // toposort returns in dependency-first order,
            // but we want leaves first for compilation
            sorted.into_iter().rev().map(|n| &self.graph[n]).collect()
        })
    }

    /// Compute compilation levels for parallel compilation.
    ///
    /// Returns a vector of levels, where each level is a set of
    /// modules that can be compiled in parallel (all their dependencies
    /// are in earlier levels).
    pub fn parallel_levels(&self) -> Option<Vec<Vec<&ModuleId>>> {
        let sorted = algo::toposort(&self.graph, None).ok()?;

        // Compute the longest path from each node to a leaf
        let mut levels: FxHashMap<NodeIndex, usize> = FxHashMap::default();

        // Process in reverse topological order (leaves first)
        for &node in sorted.iter().rev() {
            let max_dep_level = self
                .graph
                .neighbors_directed(node, Direction::Outgoing)
                .map(|dep| levels.get(&dep).copied().unwrap_or(0) + 1)
                .max()
                .unwrap_or(0);
            levels.insert(node, max_dep_level);
        }

        // Group by level
        let max_level = levels.values().copied().max().unwrap_or(0);
        let mut result: Vec<Vec<&ModuleId>> = vec![Vec::new(); max_level + 1];

        for (&node, &level) in &levels {
            result[level].push(&self.graph[node]);
        }

        Some(result)
    }

    /// Detect if there are any cycles in the dependency graph.
    ///
    /// Returns the cycle path if one exists.
    pub fn find_cycle(&self) -> Option<Vec<ModuleId>> {
        if algo::toposort(&self.graph, None).is_ok() {
            return None;
        }

        // Find a cycle using DFS
        let scc = algo::kosaraju_scc(&self.graph);
        for component in scc {
            if component.len() > 1 {
                return Some(
                    component
                        .into_iter()
                        .map(|n| self.graph[n].clone())
                        .collect(),
                );
            }
            // Check self-loop
            if component.len() == 1 {
                let node = component[0];
                if self.graph.contains_edge(node, node) {
                    return Some(vec![self.graph[node].clone()]);
                }
            }
        }

        None
    }

    /// Get all modules in the graph.
    pub fn modules(&self) -> impl Iterator<Item = &ModuleId> {
        self.graph.node_weights()
    }

    /// Number of modules in the graph.
    pub fn len(&self) -> usize {
        self.graph.node_count()
    }

    /// Whether the graph is empty.
    pub fn is_empty(&self) -> bool {
        self.graph.node_count() == 0
    }

    /// Number of dependency edges.
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// Get leaf modules (modules with no dependencies).
    pub fn leaf_modules(&self) -> Vec<&ModuleId> {
        self.graph
            .node_indices()
            .filter(|&n| {
                self.graph
                    .neighbors_directed(n, Direction::Outgoing)
                    .next()
                    .is_none()
            })
            .map(|n| &self.graph[n])
            .collect()
    }

    /// Get root modules (modules that nothing depends on).
    pub fn root_modules(&self) -> Vec<&ModuleId> {
        self.graph
            .node_indices()
            .filter(|&n| {
                self.graph
                    .neighbors_directed(n, Direction::Incoming)
                    .next()
                    .is_none()
            })
            .map(|n| &self.graph[n])
            .collect()
    }
}

impl Default for DependencyGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_some<T>(value: Option<T>, context: &str) -> T {
        match value {
            Some(val) => val,
            None => panic!("Expected Some value: {}", context),
        }
    }

    fn id(s: &str) -> ModuleId {
        ModuleId::new(s)
    }

    #[test]
    fn test_empty_graph() {
        let graph = DependencyGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.topological_order(), Some(vec![]));
    }

    #[test]
    fn test_simple_dependency() {
        let mut graph = DependencyGraph::new();
        graph.add_module(id("a"));
        graph.add_module(id("b"));
        graph.add_dependency(&id("a"), &id("b")); // a depends on b

        let deps = graph.dependencies(&id("a"));
        assert_eq!(deps.len(), 1);
        assert_eq!(deps[0], &id("b"));

        let rev = graph.reverse_dependencies(&id("b"));
        assert_eq!(rev.len(), 1);
        assert_eq!(rev[0], &id("a"));
    }

    #[test]
    fn test_topological_order() {
        let mut graph = DependencyGraph::new();
        // c → b → a (c depends on b, b depends on a)
        graph.add_dependency(&id("c"), &id("b"));
        graph.add_dependency(&id("b"), &id("a"));

        let order = expect_some(graph.topological_order(), "topological order");
        // Should compile a first, then b, then c
        let a_pos = expect_some(order.iter().position(|m| *m == &id("a")), "position a");
        let b_pos = expect_some(order.iter().position(|m| *m == &id("b")), "position b");
        let c_pos = expect_some(order.iter().position(|m| *m == &id("c")), "position c");

        assert!(a_pos < b_pos, "a should come before b");
        assert!(b_pos < c_pos, "b should come before c");
    }

    #[test]
    fn test_parallel_levels() {
        let mut graph = DependencyGraph::new();
        // d depends on b and c; b and c depend on a
        graph.add_dependency(&id("d"), &id("b"));
        graph.add_dependency(&id("d"), &id("c"));
        graph.add_dependency(&id("b"), &id("a"));
        graph.add_dependency(&id("c"), &id("a"));

        let levels = expect_some(graph.parallel_levels(), "parallel levels");
        assert_eq!(levels.len(), 3); // Level 0: a, Level 1: b+c, Level 2: d

        assert!(levels[0].contains(&&id("a")));
        assert!(levels[1].contains(&&id("b")));
        assert!(levels[1].contains(&&id("c")));
        assert!(levels[2].contains(&&id("d")));
    }

    #[test]
    fn test_cycle_detection() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("a"), &id("b"));
        graph.add_dependency(&id("b"), &id("a")); // cycle!

        assert!(graph.find_cycle().is_some());
        assert!(graph.topological_order().is_none());
    }

    #[test]
    fn test_no_cycle() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("a"), &id("b"));
        graph.add_dependency(&id("b"), &id("c"));

        assert!(graph.find_cycle().is_none());
    }

    #[test]
    fn test_leaf_and_root_modules() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("app"), &id("lib"));
        graph.add_dependency(&id("lib"), &id("core"));

        let leaves = graph.leaf_modules();
        assert_eq!(leaves.len(), 1);
        assert_eq!(leaves[0], &id("core"));

        let roots = graph.root_modules();
        assert_eq!(roots.len(), 1);
        assert_eq!(roots[0], &id("app"));
    }

    #[test]
    fn test_transitive_reverse_deps() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency(&id("c"), &id("b"));
        graph.add_dependency(&id("b"), &id("a"));

        let trans = graph.transitive_reverse_dependencies(&id("a"));
        assert_eq!(trans.len(), 2);
        // Both b and c should be in the result
        let ids: Vec<_> = trans.iter().map(|m| m.path.as_str()).collect();
        assert!(ids.contains(&"b"));
        assert!(ids.contains(&"c"));
    }
}
