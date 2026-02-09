// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive REPL for Eclexia.
//!
//! Features:
//! - Multi-line input (auto-detect incomplete expressions)
//! - History persistence (XDG data directory)
//! - :type command for type inference
//! - :shadow for shadow price display
//! - :resources for resource tracking
//! - :ast for AST inspection
//! - :info for symbol lookup
//! - :env for environment display

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

/// Run the interactive REPL.
pub fn run() -> miette::Result<()> {
    println!("Eclexia REPL v0.1.0");
    println!("Type :help for help, :quit to exit");
    println!("Multi-line input: use {{ to start a block, }} to end");
    println!();

    let mut rl = DefaultEditor::new()
        .map_err(|e| miette::miette!("Failed to create editor: {}", e))?;

    // Try to load history
    let history_path = dirs::data_dir()
        .map(|d| d.join("eclexia").join("repl_history"))
        .unwrap_or_else(|| std::path::PathBuf::from(".eclexia_history"));

    let _ = rl.load_history(&history_path);

    let mut state = ReplState::new();

    loop {
        let prompt = if state.multiline_buffer.is_some() { "...> " } else { "ecl> " };

        match rl.readline(prompt) {
            Ok(line) => {
                let trimmed = line.trim();

                // Handle empty lines in multiline mode
                if trimmed.is_empty() && state.multiline_buffer.is_none() {
                    continue;
                }

                let _ = rl.add_history_entry(&line);

                // Multi-line continuation
                if let Some(ref mut buf) = state.multiline_buffer {
                    buf.push('\n');
                    buf.push_str(&line);

                    // Check if braces are balanced
                    if braces_balanced(buf) {
                        let complete = buf.clone();
                        state.multiline_buffer = None;
                        eval_line(&complete, &mut state);
                    }
                    continue;
                }

                // Handle REPL commands
                if trimmed.starts_with(':') {
                    match handle_command(trimmed, &mut state) {
                        CommandResult::Continue => continue,
                        CommandResult::Quit => break,
                    }
                }

                // Check for incomplete input (unbalanced braces)
                if !braces_balanced(trimmed) {
                    state.multiline_buffer = Some(trimmed.to_string());
                    continue;
                }

                // Parse and evaluate
                eval_line(trimmed, &mut state);
            }
            Err(ReadlineError::Interrupted) => {
                // Cancel multiline input on Ctrl+C
                if state.multiline_buffer.is_some() {
                    state.multiline_buffer = None;
                    println!("(cancelled)");
                } else {
                    println!("^C");
                }
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

/// REPL state persisted across evaluations.
struct ReplState {
    /// Buffer for multi-line input.
    multiline_buffer: Option<String>,
    /// Evaluation counter (for variable naming).
    eval_count: u64,
    /// Accumulated definitions (carried across REPL lines).
    definitions: Vec<String>,
}

impl ReplState {
    fn new() -> Self {
        Self {
            multiline_buffer: None,
            eval_count: 0,
            definitions: Vec::new(),
        }
    }
}

/// Check if braces, parens, and brackets are balanced.
fn braces_balanced(s: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut prev_char = '\0';

    for ch in s.chars() {
        if ch == '"' && prev_char != '\\' {
            in_string = !in_string;
        }
        if !in_string {
            match ch {
                '{' | '(' | '[' => depth += 1,
                '}' | ')' | ']' => depth -= 1,
                _ => {}
            }
        }
        prev_char = ch;
    }

    depth <= 0
}

enum CommandResult {
    Continue,
    Quit,
}

fn handle_command(cmd: &str, state: &mut ReplState) -> CommandResult {
    match cmd {
        ":quit" | ":q" | ":exit" => CommandResult::Quit,
        ":help" | ":h" | ":?" => {
            println!("Available commands:");
            println!("  :help, :h, :?       Show this help");
            println!("  :quit, :q           Exit the REPL");
            println!("  :type <expr>        Show the type of an expression");
            println!("  :ast <expr>         Show the AST of an expression");
            println!("  :shadow             Show current shadow prices");
            println!("  :resources          Show resource usage summary");
            println!("  :env                Show defined symbols");
            println!("  :clear              Clear the screen");
            println!("  :reset              Reset REPL state");
            println!();
            println!("Multi-line input:");
            println!("  Start a block with {{ and the REPL will wait for }}");
            println!("  Press Ctrl+C to cancel multi-line input");
            CommandResult::Continue
        }
        ":clear" => {
            print!("\x1B[2J\x1B[1;1H");
            CommandResult::Continue
        }
        ":reset" => {
            state.definitions.clear();
            state.eval_count = 0;
            println!("REPL state reset.");
            CommandResult::Continue
        }
        ":env" => {
            if state.definitions.is_empty() {
                println!("No definitions in scope.");
            } else {
                println!("Definitions in scope:");
                for def in &state.definitions {
                    // Show first line of each definition
                    let first_line = def.lines().next().unwrap_or(def);
                    println!("  {}", first_line);
                }
            }
            CommandResult::Continue
        }
        ":shadow" => {
            // Use the runtime shadow price registry (default prices)
            let registry = eclexia_runtime::ShadowPriceRegistry::new();
            let prices = registry.get_all_prices();
            println!("Shadow prices:");
            if prices.is_empty() {
                println!("  (no prices registered)");
            } else {
                for price in &prices {
                    println!("  {} ({:?}) = {:.6}", price.resource, price.dimension, price.price);
                }
            }
            CommandResult::Continue
        }
        ":resources" => {
            // Use the Runtime to get resource stats
            let runtime = eclexia_runtime::Runtime::new();
            let stats = runtime.get_stats();
            println!("Resource tracking:");
            println!("  Energy: {:.2} J", stats.total_energy);
            println!("  Time:   {:.2} ms", stats.total_time * 1000.0);
            println!("  Memory: {:.0} B", stats.total_memory);
            println!("  Carbon: {:.4} gCO2e", stats.total_carbon);
            println!("  Total tracked: {}", stats.total_resources);
            CommandResult::Continue
        }
        _ if cmd.starts_with(":type ") => {
            let expr = &cmd[6..];
            show_type(expr, state);
            CommandResult::Continue
        }
        _ if cmd.starts_with(":t ") => {
            let expr = &cmd[3..];
            show_type(expr, state);
            CommandResult::Continue
        }
        _ if cmd.starts_with(":ast ") => {
            let expr = &cmd[5..];
            show_ast(expr);
            CommandResult::Continue
        }
        _ => {
            println!("Unknown command: {}. Type :help for help.", cmd);
            CommandResult::Continue
        }
    }
}

/// Show the inferred type of an expression.
fn show_type(expr: &str, state: &ReplState) {
    let source = wrap_in_function(expr, state);

    let (file, errors) = eclexia_parser::parse(&source);
    if !errors.is_empty() {
        for err in &errors {
            eprintln!("Parse error: {}", err.format_with_source(&source));
        }
        return;
    }

    let type_errors = eclexia_typeck::check(&file);
    // Even with type errors, try to show the inferred type
    if !type_errors.is_empty() {
        for err in &type_errors {
            eprintln!("Type warning: {}", err.format_with_source(&source));
        }
    }

    // Find the __repl_result__ function and report its return type
    for item in &file.items {
        if let eclexia_ast::Item::Function(func) = item {
            if func.name.as_str() == "__repl_result__" {
                if let Some(ret_ty) = &func.return_type {
                    let ty = &file.types[*ret_ty];
                    println!("{} : {:?}", expr, ty.kind);
                } else {
                    // Use type inference result
                    println!("{} : (inferred, run :type on a typed expression)", expr);
                }
                return;
            }
        }
    }

    println!("{} : (could not determine type)", expr);
}

/// Show the AST of an expression.
fn show_ast(expr: &str) {
    let source = format!("def __repl__() -> _ {{ {} }}", expr);

    let (file, errors) = eclexia_parser::parse(&source);
    if !errors.is_empty() {
        for err in &errors {
            eprintln!("Parse error: {}", err.format_with_source(&source));
        }
        return;
    }

    // Find the function body and print AST
    for item in &file.items {
        if let eclexia_ast::Item::Function(func) = item {
            if let Some(expr_id) = func.body.expr {
                println!("{:#?}", file.exprs[expr_id]);
            } else if !func.body.stmts.is_empty() {
                for stmt_id in &func.body.stmts {
                    println!("{:#?}", file.stmts[*stmt_id]);
                }
            }
            return;
        }
    }

    println!("(no AST produced)");
}

/// Wrap an expression in a function for evaluation, including accumulated definitions.
fn wrap_in_function(expr: &str, state: &ReplState) -> String {
    let mut source = String::new();

    // Include accumulated definitions
    for def in &state.definitions {
        source.push_str(def);
        source.push('\n');
    }

    source.push_str(&format!(
        r#"def __repl_result__() -> _ {{
    {}
}}
def main() -> Unit {{
    let result = __repl_result__()
    println(result)
}}"#,
        expr
    ));

    source
}

fn eval_line(line: &str, state: &mut ReplState) {
    // Check if this is a definition (def, fn, type, struct, const, etc.)
    let trimmed = line.trim();
    if trimmed.starts_with("def ")
        || trimmed.starts_with("fn ")
        || trimmed.starts_with("type ")
        || trimmed.starts_with("struct ")
        || trimmed.starts_with("const ")
    {
        // Validate it parses
        let (_, errors) = eclexia_parser::parse(trimmed);
        if errors.is_empty() {
            state.definitions.push(trimmed.to_string());
            println!("(defined)");
        } else {
            for err in &errors {
                let source_for_error = trimmed;
                eprintln!("Error: {}", err.format_with_source(source_for_error));
            }
        }
        return;
    }

    state.eval_count += 1;
    let source = wrap_in_function(line, state);

    let (file, errors) = eclexia_parser::parse(&source);
    if !errors.is_empty() {
        for err in &errors {
            eprintln!("Error: {}", err.format_with_source(&source));
        }
        return;
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);
    if !type_errors.is_empty() {
        for err in &type_errors {
            eprintln!("Type error: {}", err.format_with_source(&source));
        }
        return;
    }

    // Evaluate
    match eclexia_interp::run(&file) {
        Ok(_) => {}
        Err(e) => eprintln!("Runtime error: {}", e),
    }
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
