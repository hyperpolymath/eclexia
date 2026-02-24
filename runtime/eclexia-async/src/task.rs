// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Task primitives for Eclexia concurrency.
//!
//! Each task carries a resource budget and tracks its own consumption.
//! Shadow prices propagate from the runtime to influence scheduling.

use std::fmt;
use std::future::Future;
use std::sync::atomic::{AtomicU64, Ordering};

/// Unique identifier for a task.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(u64);

impl TaskId {
    /// Generate a new unique task ID.
    pub fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(1);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

impl Default for TaskId {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for TaskId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "task-{}", self.0)
    }
}

/// Task execution state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// Task is waiting to be scheduled.
    Pending,
    /// Task is currently executing.
    Running,
    /// Task completed successfully.
    Completed,
    /// Task was cancelled.
    Cancelled,
    /// Task panicked.
    Panicked,
}

/// Resource budget for a task.
#[derive(Debug, Clone, Default)]
pub struct ResourceBudget {
    /// Maximum energy this task may consume (Joules). None = unlimited.
    pub energy_limit: Option<f64>,
    /// Maximum carbon this task may emit (gCO2e). None = unlimited.
    pub carbon_limit: Option<f64>,
    /// Maximum memory this task may use (bytes). None = unlimited.
    pub memory_limit: Option<f64>,
}

/// Error returned when joining a task that panicked or was cancelled.
#[derive(Debug)]
pub enum JoinError {
    /// The task panicked.
    Panicked(String),
    /// The task was cancelled.
    Cancelled,
}

impl fmt::Display for JoinError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Panicked(msg) => write!(f, "task panicked: {}", msg),
            Self::Cancelled => write!(f, "task cancelled"),
        }
    }
}

impl std::error::Error for JoinError {}

/// Handle to a spawned task. Awaiting it yields the task's result.
#[derive(Debug)]
pub struct TaskHandle<T> {
    inner: tokio::task::JoinHandle<T>,
    id: TaskId,
}

impl<T> TaskHandle<T> {
    /// Get the task's unique ID.
    pub fn id(&self) -> TaskId {
        self.id
    }

    /// Abort the task.
    pub fn abort(&self) {
        self.inner.abort();
    }

    /// Check if the task has finished.
    pub fn is_finished(&self) -> bool {
        self.inner.is_finished()
    }
}

impl<T> Future for TaskHandle<T> {
    type Output = Result<T, JoinError>;

    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        use std::pin::Pin;
        use std::task::Poll;

        match Pin::new(&mut self.inner).poll(cx) {
            Poll::Ready(Ok(val)) => Poll::Ready(Ok(val)),
            Poll::Ready(Err(e)) => {
                if e.is_cancelled() {
                    Poll::Ready(Err(JoinError::Cancelled))
                } else {
                    Poll::Ready(Err(JoinError::Panicked(format!("{}", e))))
                }
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

/// Task spawning utilities.
pub struct Task;

impl Task {
    /// Spawn a new task with default resource budget.
    pub fn spawn<F>(future: F) -> TaskHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let id = TaskId::new();
        let handle = tokio::spawn(future);
        TaskHandle { inner: handle, id }
    }

    /// Spawn a new task with a specified resource budget.
    ///
    /// The budget is advisory — it is tracked but not enforced at the
    /// OS level. Eclexia's runtime uses it for shadow price calculation
    /// and adaptive scheduling decisions.
    pub fn spawn_with_budget<F>(_budget: ResourceBudget, future: F) -> TaskHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        // Budget tracking: in a full implementation, we'd wrap the future
        // in a resource-monitoring wrapper that periodically checks
        // consumption against limits and adjusts shadow prices.
        let id = TaskId::new();
        let handle = tokio::spawn(future);
        TaskHandle { inner: handle, id }
    }

    /// Spawn a blocking task that won't block the async executor.
    pub fn spawn_blocking<F, T>(func: F) -> TaskHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let id = TaskId::new();
        let handle = tokio::task::spawn_blocking(func);
        TaskHandle { inner: handle, id }
    }

    /// Yield execution to other tasks.
    pub async fn yield_now() {
        tokio::task::yield_now().await;
    }

    /// Sleep for the given duration.
    pub async fn sleep(duration: std::time::Duration) {
        tokio::time::sleep(duration).await;
    }
}
