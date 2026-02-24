// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Linting and static analysis for Eclexia code.

pub mod diagnostics;
pub mod rules;

use diagnostics::{Diagnostic, Severity};
use eclexia_ast::SourceFile;
use std::collections::HashMap;

/// Context provided to lint rules.
pub struct LintContext<'a> {
    /// The source file being linted.
    pub file: &'a SourceFile,
    /// The original source code.
    pub source: &'a str,
    /// Configuration options.
    pub config: &'a LintConfig,
}

/// Lint configuration.
#[derive(Debug, Clone)]
pub struct LintConfig {
    /// Maximum line length.
    pub max_line_length: usize,
    /// Rule-specific configuration.
    pub rule_config: HashMap<String, RuleConfig>,
}

impl Default for LintConfig {
    fn default() -> Self {
        Self {
            max_line_length: 100,
            rule_config: HashMap::new(),
        }
    }
}

/// Rule-specific configuration.
#[derive(Debug, Clone)]
pub struct RuleConfig {
    /// Whether this rule is enabled.
    pub enabled: bool,
    /// Rule-specific settings.
    pub settings: HashMap<String, String>,
}

impl Default for RuleConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            settings: HashMap::new(),
        }
    }
}

/// Trait for lint rules.
pub trait LintRule {
    /// Name of the rule (e.g., "unused_variable").
    fn name(&self) -> &str;

    /// Severity of this rule's violations.
    fn severity(&self) -> Severity;

    /// Description of what this rule checks.
    fn description(&self) -> &str;

    /// Check the source file and return diagnostics.
    fn check(&self, ctx: &LintContext) -> Vec<Diagnostic>;
}

/// Main linter that runs all rules.
pub struct Linter {
    rules: Vec<Box<dyn LintRule>>,
    config: LintConfig,
}

impl Linter {
    /// Create a new linter with default rules.
    pub fn new() -> Self {
        Self::with_config(LintConfig::default())
    }

    /// Create a new linter with custom configuration.
    pub fn with_config(config: LintConfig) -> Self {
        let mut linter = Self {
            rules: Vec::new(),
            config,
        };

        // Register core rules
        linter.add_rule(Box::new(rules::UnusedVariableRule));
        linter.add_rule(Box::new(rules::UnreachableCodeRule));
        linter.add_rule(Box::new(rules::LongLineRule));
        linter.add_rule(Box::new(rules::TrailingWhitespaceRule));

        // Register economics-specific rules
        linter.add_rule(Box::new(rules::UnboundedResourceRule));
        linter.add_rule(Box::new(rules::NegativeResourceRule));

        linter
    }

    /// Add a custom rule to the linter.
    pub fn add_rule(&mut self, rule: Box<dyn LintRule>) {
        self.rules.push(rule);
    }

    /// Lint a source file and return all diagnostics.
    pub fn lint(&self, file: &SourceFile, source: &str) -> Vec<Diagnostic> {
        let ctx = LintContext {
            file,
            source,
            config: &self.config,
        };

        let mut diagnostics = Vec::new();

        for rule in &self.rules {
            // Check if rule is enabled
            if let Some(rule_config) = self.config.rule_config.get(rule.name()) {
                if !rule_config.enabled {
                    continue;
                }
            }

            // Run the rule
            let rule_diagnostics = rule.check(&ctx);
            diagnostics.extend(rule_diagnostics);
        }

        // Sort diagnostics by span start position
        diagnostics.sort_by_key(|d| d.span.start);

        diagnostics
    }

    /// Format diagnostics for display.
    pub fn format_diagnostics(&self, diagnostics: &[Diagnostic], source: &str) -> String {
        let mut output = String::new();

        for diagnostic in diagnostics {
            output.push_str(&diagnostic.format_with_source(source));
            output.push('\n');
        }

        output
    }
}

impl Default for Linter {
    fn default() -> Self {
        Self::new()
    }
}
