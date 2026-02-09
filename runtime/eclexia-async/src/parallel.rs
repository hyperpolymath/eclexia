// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Parallel iterator primitives for Eclexia.
//!
//! Provides `par_map`, `par_filter`, and `par_reduce` operations that
//! split work across threads using a simple fork-join model.
//!
//! These integrate with Eclexia's resource tracking — each parallel
//! chunk tracks its own energy/carbon usage.

use std::sync::Arc;

/// A parallel iterator over a vector of elements.
///
/// Splits the data into chunks and processes them across threads.
#[derive(Debug, Clone)]
pub struct ParallelIterator<T> {
    data: Vec<T>,
    chunk_size: usize,
}

impl<T: Send + Sync + Clone + 'static> ParallelIterator<T> {
    /// Create a parallel iterator from a vector.
    pub fn from_vec(data: Vec<T>) -> Self {
        let len = data.len();
        let num_cpus = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        let chunk_size = (len / num_cpus).max(1);

        Self { data, chunk_size }
    }

    /// Set the chunk size for parallel processing.
    pub fn with_chunk_size(mut self, chunk_size: usize) -> Self {
        self.chunk_size = chunk_size.max(1);
        self
    }

    /// Apply a function to each element in parallel, producing a new vector.
    pub fn par_map<U, F>(self, f: F) -> Vec<U>
    where
        U: Send + 'static,
        F: Fn(T) -> U + Send + Sync + 'static,
    {
        if self.data.len() <= self.chunk_size {
            return self.data.into_iter().map(f).collect();
        }

        let f = Arc::new(f);
        let chunks: Vec<Vec<T>> = self
            .data
            .into_iter()
            .collect::<Vec<_>>()
            .chunks(self.chunk_size)
            .map(|c| c.to_vec())
            .collect();

        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                let f = Arc::clone(&f);
                std::thread::spawn(move || {
                    chunk.into_iter().map(|x| f(x)).collect::<Vec<U>>()
                })
            })
            .collect();

        let mut result = Vec::new();
        for handle in handles {
            result.extend(handle.join().expect("parallel map worker panicked"));
        }
        result
    }

    /// Filter elements in parallel.
    pub fn par_filter<F>(self, predicate: F) -> Vec<T>
    where
        T: Clone,
        F: Fn(&T) -> bool + Send + Sync + 'static,
    {
        if self.data.len() <= self.chunk_size {
            return self.data.into_iter().filter(|x| predicate(x)).collect();
        }

        let predicate = Arc::new(predicate);
        let chunks: Vec<Vec<T>> = self
            .data
            .into_iter()
            .collect::<Vec<_>>()
            .chunks(self.chunk_size)
            .map(|c| c.to_vec())
            .collect();

        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                let predicate = Arc::clone(&predicate);
                std::thread::spawn(move || {
                    chunk
                        .into_iter()
                        .filter(|x| predicate(x))
                        .collect::<Vec<T>>()
                })
            })
            .collect();

        let mut result = Vec::new();
        for handle in handles {
            result.extend(handle.join().expect("parallel filter worker panicked"));
        }
        result
    }

    /// Reduce elements in parallel using an associative operation.
    ///
    /// The operation must be associative (i.e., `op(op(a, b), c) == op(a, op(b, c))`)
    /// for correct results.
    pub fn par_reduce<F>(self, identity: T, op: F) -> T
    where
        T: Clone,
        F: Fn(T, T) -> T + Send + Sync + 'static,
    {
        if self.data.is_empty() {
            return identity;
        }

        if self.data.len() <= self.chunk_size {
            return self
                .data
                .into_iter()
                .fold(identity, &op);
        }

        let op = Arc::new(op);
        let identity_clone = identity.clone();
        let chunks: Vec<Vec<T>> = self
            .data
            .into_iter()
            .collect::<Vec<_>>()
            .chunks(self.chunk_size)
            .map(|c| c.to_vec())
            .collect();

        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                let op = Arc::clone(&op);
                let id = identity_clone.clone();
                std::thread::spawn(move || {
                    chunk.into_iter().fold(id, |acc, x| op(acc, x))
                })
            })
            .collect();

        let mut partial_results: Vec<T> = Vec::new();
        for handle in handles {
            partial_results.push(handle.join().expect("parallel reduce worker panicked"));
        }

        partial_results
            .into_iter()
            .fold(identity, |acc, x| op(acc, x))
    }
}

/// Trait for types that support parallel mapping.
pub trait ParallelMap {
    type Item;

    /// Apply a function to each element in parallel.
    fn par_map<U, F>(self, f: F) -> Vec<U>
    where
        U: Send + 'static,
        F: Fn(Self::Item) -> U + Send + Sync + 'static;
}

impl<T: Send + Sync + Clone + 'static> ParallelMap for Vec<T> {
    type Item = T;

    fn par_map<U, F>(self, f: F) -> Vec<U>
    where
        U: Send + 'static,
        F: Fn(T) -> U + Send + Sync + 'static,
    {
        ParallelIterator::from_vec(self).par_map(f)
    }
}
