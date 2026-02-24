// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Concurrency primitives for asynchronous programming.
//!
//! This module provides structured concurrency with tasks, channels,
//! and synchronization primitives. All operations are resource-tracked:
//! spawning tasks and sending messages consume energy and carbon budgets.
//!
//! Backed by the eclexia-async runtime crate (executor, channel, task modules).

// === Task API ===

/// Spawn a function as a concurrent task.
///
/// The spawned function runs concurrently and returns a handle
/// that can be awaited to retrieve the result.
///
/// # Example
/// ```
/// let handle = spawn(|| expensive_computation(42))
/// let result = await(handle)
/// ```
@builtin("task_spawn")
fn spawn(f: () -> T) -> Task[T];

/// Await a task handle, blocking until the result is available.
///
/// # Example
/// ```
/// let result = await(handle)
/// ```
@builtin("task_await")
fn await(task: Task[T]) -> T;

/// Yield execution to the scheduler, allowing other tasks to run.
///
/// # Example
/// ```
/// yield_now()
/// ```
@builtin("task_yield")
fn yield_now() -> ();

/// Sleep for the specified number of milliseconds.
///
/// # Example
/// ```
/// sleep(1000)  // sleep for 1 second
/// ```
@builtin("task_sleep")
fn sleep(millis: Int) -> ();

// === Channel API ===

/// Create a new unbounded channel for message passing between tasks.
///
/// Returns a pair of (sender, receiver) endpoints.
///
/// # Example
/// ```
/// let (tx, rx) = channel()
/// spawn(|| { send(tx, 42) })
/// let value = recv(rx)
/// ```
@builtin("channel_create")
fn channel() -> (Sender[T], Receiver[T]);

/// Send a value through a channel sender.
///
/// # Example
/// ```
/// send(tx, "hello")
/// ```
@builtin("channel_send")
fn send(sender: Sender[T], value: T) -> ();

/// Receive a value from a channel receiver.
///
/// Blocks until a value is available.
///
/// # Example
/// ```
/// let msg = recv(rx)
/// ```
@builtin("channel_recv")
fn recv(receiver: Receiver[T]) -> T;

/// Try to receive a value without blocking.
///
/// Returns Some(value) if available, None otherwise.
///
/// # Example
/// ```
/// match try_recv(rx) {
///     Some(v) => println("got:", v),
///     None => println("nothing yet"),
/// }
/// ```
@builtin("channel_try_recv")
fn try_recv(receiver: Receiver[T]) -> Option[T];

// === Select API ===

/// Wait on multiple channels, returning the first available value.
///
/// Takes an array of receivers and returns a tuple of (index, value)
/// indicating which channel produced the value.
///
/// # Example
/// ```
/// let (idx, val) = select([rx1, rx2, rx3])
/// ```
@builtin("channel_select")
fn select(receivers: Array[Receiver[T]]) -> (Int, T);

// === Parallel combinators ===

/// Run multiple tasks in parallel and collect all results.
///
/// # Example
/// ```
/// let results = parallel([
///     || fetch_data("url1"),
///     || fetch_data("url2"),
///     || fetch_data("url3"),
/// ])
/// ```
@builtin("parallel_all")
fn parallel(tasks: Array[() -> T]) -> Array[T];

/// Run multiple tasks in parallel, return the first to complete.
///
/// # Example
/// ```
/// let fastest = race([
///     || slow_computation(),
///     || fast_computation(),
/// ])
/// ```
@builtin("parallel_race")
fn race(tasks: Array[() -> T]) -> T;
