// SPDX-License-Identifier: PMPL-1.0-or-later

//! CLI argument parsing helpers.

use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct ParsedArgs {
    pub command: Option<String>,
    pub flags: HashMap<String, Option<String>>,
    pub positional: Vec<String>,
}

impl ParsedArgs {
    pub fn has_flag(&self, name: &str) -> bool {
        self.flags.contains_key(name)
    }

    pub fn value(&self, name: &str) -> Option<&str> {
        self.flags.get(name).and_then(|v| v.as_deref())
    }
}

pub fn parse_args(args: &[String]) -> ParsedArgs {
    let mut parsed = ParsedArgs::default();
    let mut i = 0usize;
    let mut parse_opts = true;

    while i < args.len() {
        let arg = &args[i];
        if parse_opts && arg == "--" {
            parse_opts = false;
            i += 1;
            continue;
        }

        if parse_opts {
            if let Some(long) = arg.strip_prefix("--") {
                if let Some((k, v)) = long.split_once('=') {
                    parsed.flags.insert(k.to_string(), Some(v.to_string()));
                } else if i + 1 < args.len() && !args[i + 1].starts_with('-') {
                    parsed
                        .flags
                        .insert(long.to_string(), Some(args[i + 1].clone()));
                    i += 1;
                } else {
                    parsed.flags.insert(long.to_string(), None);
                }
                i += 1;
                continue;
            }

            if let Some(shorts) = arg.strip_prefix('-') {
                if !shorts.is_empty() {
                    if shorts.len() == 1 && i + 1 < args.len() && !args[i + 1].starts_with('-') {
                        let first = shorts.chars().next().unwrap_or_default();
                        parsed
                            .flags
                            .insert(first.to_string(), Some(args[i + 1].clone()));
                        i += 2;
                        continue;
                    }
                    for ch in shorts.chars() {
                        parsed.flags.insert(ch.to_string(), None);
                    }
                    i += 1;
                    continue;
                }
            }
        }

        if parsed.command.is_none() {
            parsed.command = Some(arg.clone());
        } else {
            parsed.positional.push(arg.clone());
        }
        i += 1;
    }

    parsed
}

#[derive(Debug, Clone)]
pub struct OptionSpec {
    pub name: String,
    pub takes_value: bool,
    pub description: String,
}

#[derive(Debug, Clone, Default)]
pub struct CommandSpec {
    pub program: String,
    pub summary: String,
    pub options: Vec<OptionSpec>,
}

impl CommandSpec {
    pub fn usage(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "Usage: {} [OPTIONS] [COMMAND] [ARGS...]\n",
            self.program
        ));
        if !self.summary.is_empty() {
            out.push_str(&format!("\n{}\n", self.summary));
        }
        if !self.options.is_empty() {
            out.push_str("\nOptions:\n");
            for opt in &self.options {
                let value_hint = if opt.takes_value { " <value>" } else { "" };
                out.push_str(&format!(
                    "  --{}{}    {}\n",
                    opt.name, value_hint, opt.description
                ));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_flags_and_positional() {
        let args = vec![
            "--mode=dev".to_string(),
            "-av".to_string(),
            "run".to_string(),
            "file.ecl".to_string(),
        ];
        let parsed = parse_args(&args);
        assert_eq!(
            parsed.flags.get("mode").cloned().flatten(),
            Some("dev".to_string())
        );
        assert!(parsed.flags.contains_key("a"));
        assert!(parsed.flags.contains_key("v"));
        assert_eq!(parsed.command.as_deref(), Some("run"));
        assert_eq!(parsed.positional, vec!["file.ecl".to_string()]);
    }

    #[test]
    fn test_short_with_value_and_end_of_opts() {
        let args = vec![
            "-o".to_string(),
            "out.txt".to_string(),
            "--".to_string(),
            "--not-an-option".to_string(),
        ];
        let parsed = parse_args(&args);
        assert_eq!(
            parsed.flags.get("o").cloned().flatten(),
            Some("out.txt".to_string())
        );
        assert_eq!(parsed.command.as_deref(), Some("--not-an-option"));
    }
}
