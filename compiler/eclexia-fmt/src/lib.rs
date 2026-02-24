// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Code formatter for Eclexia.
//!
//! This crate provides AST-based formatting with economics-aware formatting
//! for resource blocks, adaptive functions, and dimensional literals.

mod printer;

use eclexia_ast::SourceFile;
use eclexia_parser::parse;

/// Formatter configuration.
#[derive(Debug, Clone)]
pub struct FormatConfig {
    /// Number of spaces per indentation level.
    pub indent_width: usize,
    /// Maximum line width before breaking.
    pub max_width: usize,
    /// Use spaces (true) or tabs (false).
    pub use_spaces: bool,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            indent_width: 4,
            max_width: 100,
            use_spaces: true,
        }
    }
}

/// Formatter for Eclexia code.
pub struct Formatter {
    config: FormatConfig,
}

impl Formatter {
    /// Create a new formatter with default configuration.
    pub fn new() -> Self {
        Self {
            config: FormatConfig::default(),
        }
    }

    /// Create a formatter with custom configuration.
    pub fn with_config(config: FormatConfig) -> Self {
        Self { config }
    }

    /// Format Eclexia source code.
    pub fn format(&self, source: &str) -> Result<String, String> {
        // Parse the source
        let (file, errors) = parse(source);

        if !errors.is_empty() {
            return Err(format!(
                "Cannot format file with parse errors: {} errors found",
                errors.len()
            ));
        }

        // Format the AST
        let formatted = self.format_file(&file, source);

        Ok(formatted)
    }

    /// Format a parsed source file.
    fn format_file(&self, file: &SourceFile, source: &str) -> String {
        let mut printer = printer::Printer::new(&self.config, source);

        for item in &file.items {
            printer.format_item(item, file);
            printer.newline();
            printer.newline();
        }

        // Remove trailing blank lines
        let result = printer.finish();
        result.trim_end().to_string() + "\n"
    }
}

impl Default for Formatter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(val) => val,
            Err(err) => panic!("Expected Ok, got Err: {:?}", err),
        }
    }

    #[test]
    fn test_format_simple_function() {
        let source = "fn add(a:Int,b:Int)->Int{a+b}";
        let formatter = Formatter::new();
        let formatted = expect_ok(formatter.format(source));

        // Should have proper spacing
        assert!(formatted.contains("fn add"));
        assert!(formatted.contains("a: Int"));
        assert!(formatted.contains("b: Int"));
    }

    #[test]
    fn test_format_preserves_semantics() {
        let source = "fn main() { let x = 42; println(x); }";
        let formatter = Formatter::new();
        let formatted = expect_ok(formatter.format(source));

        // Re-parse formatted code to ensure it's valid
        let (_, errors) = parse(&formatted);
        assert!(
            errors.is_empty(),
            "Formatted code should parse without errors"
        );
    }
}
