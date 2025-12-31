// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive REPL for Eclexia.

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

/// Run the interactive REPL.
pub fn run() -> miette::Result<()> {
    println!("Eclexia REPL v0.1.0");
    println!("Type :help for help, :quit to exit");
    println!();

    let mut rl = DefaultEditor::new().map_err(|e| miette::miette!("Failed to create editor: {}", e))?;

    // Try to load history
    let history_path = dirs::data_dir()
        .map(|d| d.join("eclexia").join("repl_history"))
        .unwrap_or_else(|| std::path::PathBuf::from(".eclexia_history"));

    let _ = rl.load_history(&history_path);

    loop {
        match rl.readline("ecl> ") {
            Ok(line) => {
                let trimmed = line.trim();

                if trimmed.is_empty() {
                    continue;
                }

                let _ = rl.add_history_entry(&line);

                // Handle REPL commands
                if trimmed.starts_with(':') {
                    match handle_command(trimmed) {
                        CommandResult::Continue => continue,
                        CommandResult::Quit => break,
                    }
                    continue;
                }

                // Parse and evaluate
                eval_line(trimmed);
            }
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!("Goodbye!");
                break;
            }
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
    }

    // Save history
    if let Some(parent) = history_path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let _ = rl.save_history(&history_path);

    Ok(())
}

enum CommandResult {
    Continue,
    Quit,
}

fn handle_command(cmd: &str) -> CommandResult {
    match cmd {
        ":quit" | ":q" | ":exit" => CommandResult::Quit,
        ":help" | ":h" | ":?" => {
            println!("Available commands:");
            println!("  :help, :h, :?    Show this help");
            println!("  :quit, :q        Exit the REPL");
            println!("  :type <expr>     Show the type of an expression");
            println!("  :shadow          Show current shadow prices");
            println!("  :resources       Show resource usage");
            println!("  :clear           Clear the screen");
            CommandResult::Continue
        }
        ":clear" => {
            print!("\x1B[2J\x1B[1;1H");
            CommandResult::Continue
        }
        ":shadow" => {
            println!("Shadow prices (not yet implemented):");
            println!("  λ_energy  = 0.0");
            println!("  λ_time    = 0.0");
            println!("  λ_memory  = 0.0");
            println!("  λ_carbon  = 0.0");
            CommandResult::Continue
        }
        ":resources" => {
            println!("Resource usage (not yet implemented):");
            println!("  Energy: 0 J");
            println!("  Time:   0 ms");
            println!("  Memory: 0 B");
            println!("  Carbon: 0 gCO2e");
            CommandResult::Continue
        }
        _ if cmd.starts_with(":type ") => {
            let expr = &cmd[6..];
            println!("Type of '{}': (not yet implemented)", expr);
            CommandResult::Continue
        }
        _ => {
            println!("Unknown command: {}. Type :help for help.", cmd);
            CommandResult::Continue
        }
    }
}

fn eval_line(line: &str) {
    // Parse as expression
    let source = format!("def __repl__() {{ {} }}", line);
    let (file, errors) = eclexia_parser::parse(&source);

    if !errors.is_empty() {
        for err in &errors {
            eprintln!("Error: {}", err);
        }
        return;
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);
    if !type_errors.is_empty() {
        for err in &type_errors {
            eprintln!("Type error: {}", err);
        }
        return;
    }

    // TODO: Evaluate and print result
    println!("(parsed {} items)", file.items.len());
}

// Helper for finding data directories
mod dirs {
    use std::path::PathBuf;

    pub fn data_dir() -> Option<PathBuf> {
        std::env::var_os("XDG_DATA_HOME")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".local/share"))
            })
    }
}
