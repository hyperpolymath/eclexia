// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Time and duration utilities for scheduling and timing.
//!
//! This module provides types and functions for working with time,
//! durations, and timestamps. Useful for carbon-aware scheduling
//! and performance measurement.

// ============================================================================
// Time Builtins
// ============================================================================

/// Get the current time in milliseconds since Unix epoch.
@builtin("time_now_ms")
fn now_ms() -> Int;

/// Get the current Unix timestamp in seconds.
@builtin("time_unix_timestamp")
fn unix_timestamp() -> Int;

/// Sleep for the specified number of milliseconds.
@builtin("time_sleep_ms")
fn sleep_ms(millis: Int) -> ();

/// Get the current hour (0-23) in local time.
@builtin("time_hour")
fn hour() -> Int;

/// Get the current day of week (0=Sunday, 6=Saturday).
@builtin("time_day_of_week")
fn day_of_week() -> Int;

/// Convert a Unix timestamp to ISO 8601 format.
@builtin("time_to_iso8601")
fn to_iso8601(timestamp: Int) -> String;

/// Parse an ISO 8601 datetime string to Unix timestamp.
@builtin("time_from_iso8601")
fn from_iso8601(iso_string: String) -> Int;

// ============================================================================
// Duration Type (Record)
// ============================================================================

/// A duration of time in milliseconds.
///
/// # Example
/// ```
/// let duration = Duration { millis: 1000 };  // 1 second
/// ```
type Duration = {
    millis: Int,
};

/// Create a duration from milliseconds.
fn from_millis(millis: Int) -> Duration {
    Duration { millis: millis }
}

/// Create a duration from seconds.
fn from_secs(secs: Int) -> Duration {
    Duration { millis: secs * 1000 }
}

/// Get duration in milliseconds.
fn as_millis(d: Duration) -> Int {
    d.millis
}

/// Get duration in seconds.
fn as_secs(d: Duration) -> Int {
    d.millis / 1000
}

/// Sleep for a duration.
fn sleep(d: Duration) -> () {
    sleep_ms(d.millis)
}

// ============================================================================
// Instant Type (Record)
// ============================================================================

/// A point in time (milliseconds since Unix epoch).
///
/// # Example
/// ```
/// let start = now();
/// // ... do work ...
/// let elapsed = duration_since(now(), start);
/// ```
type Instant = {
    timestamp_ms: Int,
};

/// Get the current instant.
fn now() -> Instant {
    Instant { timestamp_ms: now_ms() }
}

/// Calculate duration between two instants.
fn duration_since(now: Instant, earlier: Instant) -> Duration {
    let diff = now.timestamp_ms - earlier.timestamp_ms;
    Duration { millis: diff }
}

/// Get elapsed time since an instant.
fn elapsed(start: Instant) -> Duration {
    duration_since(now(), start)
}

// ============================================================================
// DateTime Type (Record)
// ============================================================================

/// A datetime with Unix timestamp.
///
/// # Example
/// ```
/// let dt = datetime_now();
/// let hour = dt_hour(dt);  // 0-23
/// ```
type DateTime = {
    unix_timestamp: Int,
};

/// Get the current datetime.
fn datetime_now() -> DateTime {
    DateTime { unix_timestamp: unix_timestamp() }
}

/// Get hour from datetime (0-23).
fn dt_hour(dt: DateTime) -> Int {
    hour()  // Note: Uses current time; full impl would parse timestamp
}

/// Get day of week from datetime (0=Sunday, 6=Saturday).
fn dt_day_of_week(dt: DateTime) -> Int {
    day_of_week()  // Note: Uses current time; full impl would parse timestamp
}

/// Convert datetime to ISO 8601 string.
fn dt_to_iso8601(dt: DateTime) -> String {
    to_iso8601(dt.unix_timestamp)
}

/// Parse ISO 8601 string to datetime.
fn dt_from_iso8601(iso_string: String) -> DateTime {
    DateTime { unix_timestamp: from_iso8601(iso_string) }
}

// ============================================================================
// Utility Functions
// ============================================================================

/// Measure execution time of an operation.
///
/// # Example
/// ```
/// let (result, duration) = measure(fn() {
///     // expensive computation
///     42
/// });
/// println("Took: " + to_string(as_millis(duration)) + "ms");
/// ```
fn measure<T>(f: fn() -> T) -> (T, Duration) {
    let start = now();
    let result = f();
    let elapsed = elapsed(start);
    (result, elapsed)
}
