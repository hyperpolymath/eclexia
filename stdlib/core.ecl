// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Core standard library module.
//!
//! Provides fundamental types and operations for all Eclexia programs.

/// Option type for values that may or may not exist.
type Option<T> {
    Some(T),
    None,
}

/// Result type for operations that can fail.
type Result<T, E> {
    Ok(T),
    Err(E),
}

/// Panic with a message and halt execution.
fn panic(message: String) -> ! {
    // TODO: Implement proper panic handling
    // For now, this will be a compiler intrinsic
    @builtin("panic")
}

/// Assert that a condition is true, panic if false.
fn assert(condition: Bool, message: String) {
    if !condition {
        panic(message)
    }
}

/// Assert equality, panic if not equal.
fn assert_eq<T>(left: T, right: T, message: String) {
    if left != right {
        panic(message)
    }
}

/// Print a value to stdout.
fn print<T>(value: T) {
    @builtin("print")
}

/// Print a value to stdout with newline.
fn println<T>(value: T) {
    @builtin("println")
}

// Option methods
impl<T> Option<T> {
    /// Returns true if the option is Some.
    fn is_some(self) -> Bool {
        match self {
            Some(_) => true,
            None => false,
        }
    }

    /// Returns true if the option is None.
    fn is_none(self) -> Bool {
        match self {
            Some(_) => false,
            None => true,
        }
    }

    /// Returns the contained Some value or panics.
    fn unwrap(self) -> T {
        match self {
            Some(value) => value,
            None => panic("called `Option::unwrap()` on a `None` value"),
        }
    }

    /// Returns the contained Some value or a default.
    fn unwrap_or(self, default: T) -> T {
        match self {
            Some(value) => value,
            None => default,
        }
    }

    /// Maps an Option<T> to Option<U> by applying a function to the contained value.
    fn map<U>(self, f: fn(T) -> U) -> Option<U> {
        match self {
            Some(value) => Some(f(value)),
            None => None,
        }
    }

    /// Returns None if the option is None, otherwise calls f with the wrapped value.
    fn and_then<U>(self, f: fn(T) -> Option<U>) -> Option<U> {
        match self {
            Some(value) => f(value),
            None => None,
        }
    }
}

// Result methods
impl<T, E> Result<T, E> {
    /// Returns true if the result is Ok.
    fn is_ok(self) -> Bool {
        match self {
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// Returns true if the result is Err.
    fn is_err(self) -> Bool {
        match self {
            Ok(_) => false,
            Err(_) => true,
        }
    }

    /// Returns the contained Ok value or panics.
    fn unwrap(self) -> T {
        match self {
            Ok(value) => value,
            Err(_) => panic("called `Result::unwrap()` on an `Err` value"),
        }
    }

    /// Returns the contained Err value or panics.
    fn unwrap_err(self) -> E {
        match self {
            Ok(_) => panic("called `Result::unwrap_err()` on an `Ok` value"),
            Err(error) => error,
        }
    }

    /// Returns the contained Ok value or a default.
    fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(value) => value,
            Err(_) => default,
        }
    }

    /// Maps a Result<T, E> to Result<U, E> by applying a function to the contained Ok value.
    fn map<U>(self, f: fn(T) -> U) -> Result<U, E> {
        match self {
            Ok(value) => Ok(f(value)),
            Err(error) => Err(error),
        }
    }

    /// Maps a Result<T, E> to Result<T, F> by applying a function to the contained Err value.
    fn map_err<F>(self, f: fn(E) -> F) -> Result<T, F> {
        match self {
            Ok(value) => Ok(value),
            Err(error) => Err(f(error)),
        }
    }

    /// Calls f if the result is Ok, otherwise returns the Err value.
    fn and_then<U>(self, f: fn(T) -> Result<U, E>) -> Result<U, E> {
        match self {
            Ok(value) => f(value),
            Err(error) => Err(error),
        }
    }
}

// Array utilities
fn array_len<T>(arr: Array<T>) -> Int {
    @builtin("array_len")
}

fn array_get<T>(arr: Array<T>, index: Int) -> Option<T> {
    @builtin("array_get")
}

fn array_push<T>(arr: Array<T>, value: T) {
    @builtin("array_push")
}

fn array_pop<T>(arr: Array<T>) -> Option<T> {
    @builtin("array_pop")
}

// String utilities
fn string_len(s: String) -> Int {
    @builtin("string_len")
}

fn string_concat(a: String, b: String) -> String {
    @builtin("string_concat")
}

fn string_substring(s: String, start: Int, end: Int) -> String {
    @builtin("string_substring")
}

// Conversion functions
fn int_to_string(n: Int) -> String {
    @builtin("int_to_string")
}

fn float_to_string(f: Float) -> String {
    @builtin("float_to_string")
}

fn string_to_int(s: String) -> Result<Int, String> {
    @builtin("string_to_int")
}

fn string_to_float(s: String) -> Result<Float, String> {
    @builtin("string_to_float")
}
