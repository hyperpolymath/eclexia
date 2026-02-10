// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Async runtime and concurrency primitives for Eclexia.
//!
//! Provides resource-aware concurrency where each task tracks its own
//! resource budget and shadow prices propagate across task boundaries.
//!
//! # Architecture
//!
//! - **Task executor**: Built on tokio, manages spawning and scheduling.
//! - **Channels**: MPSC, oneshot, and broadcast channels with backpressure.
//! - **Parallel iterators**: `par_map`, `par_filter`, `par_reduce`.
//! - **Resource-aware scheduling**: Tasks carry resource budgets; carbon-aware
//!   deferral delays low-priority work until green energy is available.
//!
//! # Usage
//!
//! ```ignore
//! use eclexia_async::{Runtime, Channel, Task};
//!
//! let rt = Runtime::new(RuntimeConfig::default());
//! let (tx, rx) = rt.channel::<i64>(32);
//!
//! rt.spawn(async move {
//!     tx.send(42).await;
//! });
//!
//! let value = rt.block_on(async move {
//!     rx.recv().await
//! });
//! ```

mod channel;
mod executor;
mod parallel;
mod task;

pub use channel::{broadcast, mpsc, oneshot, Channel, ChannelError, Receiver, Sender};
pub use executor::{Runtime, RuntimeConfig};
pub use parallel::{ParallelIterator, ParallelMap};
pub use task::{JoinError, Task, TaskHandle, TaskId, TaskState};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_creation() {
        let rt = Runtime::new(RuntimeConfig::default());
        assert!(rt.is_running());
    }

    #[test]
    fn test_mpsc_channel() {
        let rt = Runtime::new(RuntimeConfig::default());
        rt.block_on(async {
            let (tx, mut rx) = mpsc(32);
            tx.send(42i64).await.unwrap();
            let val = rx.recv().await.unwrap();
            assert_eq!(val, 42);
        });
    }

    #[test]
    fn test_oneshot_channel() {
        let rt = Runtime::new(RuntimeConfig::default());
        rt.block_on(async {
            let (tx, rx) = oneshot();
            tx.send(99i64).unwrap();
            let val = rx.await.unwrap();
            assert_eq!(val, 99);
        });
    }

    #[test]
    fn test_spawn_and_join() {
        let rt = Runtime::new(RuntimeConfig::default());
        let result = rt.block_on(async {
            let handle = Task::spawn(async { 1 + 2 });
            handle.await.unwrap()
        });
        assert_eq!(result, 3);
    }

    #[test]
    fn test_parallel_map() {
        let data = vec![1, 2, 3, 4, 5];
        let result: Vec<i64> = ParallelIterator::from_vec(data).par_map(|x| x * 2);
        assert_eq!(result, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_parallel_filter() {
        let data = vec![1, 2, 3, 4, 5, 6];
        let result: Vec<i64> = ParallelIterator::from_vec(data).par_filter(|x| x % 2 == 0);
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_parallel_reduce() {
        let data = vec![1, 2, 3, 4, 5];
        let result = ParallelIterator::from_vec(data).par_reduce(0, |acc, x| acc + x);
        assert_eq!(result, 15);
    }

    #[test]
    fn test_task_resource_tracking() {
        let rt = Runtime::new(RuntimeConfig::default());
        let result = rt.block_on(async {
            let handle = Task::spawn_with_budget(
                task::ResourceBudget {
                    energy_limit: Some(100.0),
                    carbon_limit: Some(50.0),
                    memory_limit: Some(1024.0),
                },
                async { 42 },
            );
            handle.await.unwrap()
        });
        assert_eq!(result, 42);
    }

    #[test]
    fn test_broadcast_channel() {
        let rt = Runtime::new(RuntimeConfig::default());
        rt.block_on(async {
            let (tx, mut rx1) = broadcast(16);
            let mut rx2 = tx.subscribe();

            tx.send(7).unwrap();

            assert_eq!(rx1.recv().await.unwrap(), 7);
            assert_eq!(rx2.recv().await.unwrap(), 7);
        });
    }

    #[test]
    fn test_multiple_spawns() {
        let rt = Runtime::new(RuntimeConfig::default());
        let result = rt.block_on(async {
            let mut handles = Vec::new();
            for i in 0..10 {
                handles.push(Task::spawn(async move { i * i }));
            }
            let mut results = Vec::new();
            for h in handles {
                results.push(h.await.unwrap());
            }
            results
        });
        let expected: Vec<i64> = (0..10).map(|i| i * i).collect();
        assert_eq!(result, expected);
    }
}
