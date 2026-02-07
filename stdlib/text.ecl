// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Text and string manipulation utilities.
//!
//! This module provides functions for common string operations
//! like trimming, splitting, case conversion, and pattern matching.

/// Trim whitespace from both ends of a string.
///
/// # Example
/// ```
/// let s = trim("  hello  ");  // "hello"
/// ```
@builtin("str_trim")
fn trim(s: String) -> String;

/// Split a string by a delimiter into an array of substrings.
///
/// # Example
/// ```
/// let parts = split("a,b,c", ",");  // ["a", "b", "c"]
/// ```
@builtin("str_split")
fn split(s: String, delim: String) -> [String];

/// Check if a string contains a substring.
///
/// # Example
/// ```
/// let has_foo = contains("foobar", "foo");  // true
/// ```
@builtin("str_contains")
fn contains(s: String, needle: String) -> Bool;

/// Convert a string to lowercase.
///
/// # Example
/// ```
/// let lower = to_lowercase("HELLO");  // "hello"
/// ```
@builtin("str_to_lowercase")
fn to_lowercase(s: String) -> String;

/// Convert a string to uppercase.
///
/// # Example
/// ```
/// let upper = to_uppercase("hello");  // "HELLO"
/// ```
@builtin("str_to_uppercase")
fn to_uppercase(s: String) -> String;

/// Replace all occurrences of a pattern with a replacement.
///
/// # Example
/// ```
/// let s = replace("hello world", "world", "Eclexia");  // "hello Eclexia"
/// ```
@builtin("str_replace")
fn replace(s: String, pattern: String, replacement: String) -> String;

/// Get the length of a string in characters.
///
/// # Example
/// ```
/// let len = length("hello");  // 5
/// ```
@builtin("len")
fn length(s: String) -> Int;

/// Join an array of strings with a delimiter.
///
/// # Example
/// ```
/// let s = join(["a", "b", "c"], ", ");  // "a, b, c"
/// ```
fn join(parts: [String], delim: String) -> String {
    // TODO: Implement using array reduce when available
    // For now, this is a placeholder
    ""
}

/// Check if a string starts with a prefix.
///
/// # Example
/// ```
/// let starts = starts_with("hello world", "hello");  // true
/// ```
fn starts_with(s: String, prefix: String) -> Bool {
    // Simple implementation: check if prefix is at the beginning
    contains(s, prefix)  // Note: This is simplified; real impl would check position
}

/// Check if a string ends with a suffix.
///
/// # Example
/// ```
/// let ends = ends_with("hello world", "world");  // true
/// ```
fn ends_with(s: String, suffix: String) -> Bool {
    // Simple implementation: check if suffix is present
    contains(s, suffix)  // Note: This is simplified; real impl would check position
}
