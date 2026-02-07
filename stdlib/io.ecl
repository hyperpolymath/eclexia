// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! I/O operations for files and JSON.
//!
//! This module provides functions for reading and writing files,
//! as well as JSON serialization/deserialization.

/// Read the entire contents of a file as a string.
///
/// # Example
/// ```
/// let content = read_file("data.txt");
/// ```
@builtin("read_file")
fn read_file(path: String) -> String;

/// Write a string to a file, creating it if it doesn't exist.
///
/// # Example
/// ```
/// write_file("output.txt", "Hello, world!");
/// ```
@builtin("write_file")
fn write_file(path: String, contents: String) -> ();

/// Check if a file exists at the given path.
///
/// # Example
/// ```
/// if file_exists("config.toml") {
///     let config = read_file("config.toml");
/// }
/// ```
@builtin("file_exists")
fn file_exists(path: String) -> Bool;

/// Parse a JSON string into a value.
///
/// # Example
/// ```
/// let data = parse_json("{\"name\": \"Alice\", \"age\": 30}");
/// ```
@builtin("parse_json")
fn parse_json(json_str: String) -> Value;

/// Convert a value to a JSON string.
///
/// # Example
/// ```
/// let json = to_json({"name": "Alice", "age": 30});
/// ```
@builtin("to_json")
fn to_json(value: Value) -> String;

/// Read a JSON file and parse it.
///
/// # Example
/// ```
/// let config = read_json("config.json");
/// ```
fn read_json(path: String) -> Value {
    let content = read_file(path);
    parse_json(content)
}

/// Write a value to a JSON file.
///
/// # Example
/// ```
/// write_json("output.json", {"result": 42});
/// ```
fn write_json(path: String, value: Value) -> () {
    let json = to_json(value);
    write_file(path, json)
}
