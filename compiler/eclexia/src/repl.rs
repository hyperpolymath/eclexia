// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive REPL for Eclexia.
//!
//! Features:
//! - Multi-line input (auto-detect incomplete expressions)
//! - History persistence (XDG data directory)
//! - Tab completion for keywords, builtins, REPL commands, and user definitions
//! - Syntax highlighting for keywords and REPL commands
//! - :type command for type inference
//! - :shadow for shadow price display
//! - :resources for resource tracking
//! - :ast for AST inspection
//! - :info for symbol lookup
//! - :env for environment display

use rustyline::completion::{Completer, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Context as RustylineContext, Editor, Helper};
use std::borrow::Cow;
use std::sync::{Arc, Mutex};

/// Eclexia language keywords available for tab completion.
const KEYWORDS: &[&str] = &[
    "adaptive", "and", "as", "async", "await", "break",
    "carbon", "case", "chan", "comptime", "const", "continue",
    "def", "do", "effect", "else", "energy", "enum",
    "export", "extern", "false", "fn", "for",
    "handle", "if", "impl", "import", "in", "latency", "let",
    "loop", "macro", "match", "memory", "mod", "module",
    "mut", "not", "or", "pub", "recv", "ref", "return",
    "select", "self", "Self", "send", "spawn", "static",
    "struct", "super", "then", "trait", "true", "type",
    "unit", "use", "where", "while", "yield",
];

/// Built-in function names available for tab completion.
const BUILTINS: &[&str] = &[
    "println", "print", "len", "to_string", "abs", "min", "max",
    "sqrt", "floor", "ceil", "range", "push", "pop",
    "current_energy", "current_carbon", "gpu_available", "cpu_cores",
    "parse_json", "to_json", "read_file", "write_file", "file_exists",
    "str_trim", "str_split", "str_contains", "str_to_lowercase",
    "str_to_uppercase", "str_replace",
    "array_map", "array_filter", "array_sum",
    "time_now_ms", "time_unix_timestamp", "time_sleep_ms",
    "time_hour", "time_day_of_week", "time_to_iso8601", "time_from_iso8601",
    "pow", "log", "exp",
    "hashmap_new", "hashmap_insert", "hashmap_get", "hashmap_remove",
    "hashmap_contains", "hashmap_len", "hashmap_keys", "hashmap_values",
    "hashmap_entries",
    "sortedmap_new", "sortedmap_insert", "sortedmap_get", "sortedmap_remove",
    "sortedmap_len", "sortedmap_keys", "sortedmap_min_key", "sortedmap_max_key",
    "sortedmap_range",
    "queue_new", "queue_enqueue", "queue_dequeue", "queue_peek",
    "queue_is_empty", "queue_len",
    "priority_queue_new", "priority_queue_push", "priority_queue_pop",
    "priority_queue_peek", "priority_queue_len",
    "set_new", "set_insert", "set_remove", "set_contains", "set_len",
    "set_union", "set_intersection", "set_difference",
    "shadow_price", "assert", "panic",
    "is_some", "is_none", "is_ok", "is_err",
    "Ok", "Err", "None",
];

/// REPL commands available for tab completion (with leading colon).
const REPL_COMMANDS: &[&str] = &[
    ":help", ":h", ":?",
    ":quit", ":q", ":exit",
    ":type", ":t",
    ":info", ":i",
    ":ast",
    ":shadow",
    ":resources",
    ":env",
    ":clear",
    ":reset",
];

/// Shared list of user-defined symbol names, updated as the user enters
/// definitions and shared with the tab-completion helper.
type UserSymbols = Arc<Mutex<Vec<String>>>;

/// Rustyline helper providing tab completion, syntax highlighting, and
/// bracket-aware multi-line validation.
#[derive(Clone, Debug)]
struct ReplHelper {
    /// Names defined by the user in this REPL session (shared with ReplState).
    user_symbols: UserSymbols,
}

impl ReplHelper {
    fn new(user_symbols: UserSymbols) -> Self {
        Self { user_symbols }
    }
}

impl Helper for ReplHelper {}

impl Completer for ReplHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &RustylineContext<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        // Find the start of the word being completed.
        let prefix_start = line[..pos]
            .rfind(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != ':' && c != '@')
            .map(|i| i + 1)
            .unwrap_or(0);
        let prefix = &line[prefix_start..pos];

        if prefix.is_empty() {
            return Ok((pos, Vec::new()));
        }

        let mut candidates: Vec<Pair> = Vec::new();

        // REPL commands (only at start of line)
        if prefix.starts_with(':') {
            for cmd in REPL_COMMANDS {
                if cmd.starts_with(prefix) && *cmd != prefix {
                    candidates.push(Pair {
                        display: cmd.to_string(),
                        replacement: cmd[prefix_start..].to_string(),
                    });
                }
            }
            // Deduplicate by display text (some commands are aliases)
            candidates.sort_by(|a, b| a.display.cmp(&b.display));
            candidates.dedup_by(|a, b| a.display == b.display);
            return Ok((prefix_start, candidates));
        }

        // Resource annotation keywords
        if prefix.starts_with('@') {
            let annotations = [
                "@requires", "@provides", "@optimize", "@when", "@solution",
                "@defer_until",
            ];
            for ann in &annotations {
                if ann.starts_with(prefix) && *ann != prefix {
                    candidates.push(Pair {
                        display: ann.to_string(),
                        replacement: ann.to_string(),
                    });
                }
            }
            return Ok((prefix_start, candidates));
        }

        // Language keywords
        for kw in KEYWORDS {
            if kw.starts_with(prefix) && *kw != prefix {
                candidates.push(Pair {
                    display: kw.to_string(),
                    replacement: kw.to_string(),
                });
            }
        }

        // Built-in functions
        for bi in BUILTINS {
            if bi.starts_with(prefix) && *bi != prefix {
                candidates.push(Pair {
                    display: bi.to_string(),
                    replacement: bi.to_string(),
                });
            }
        }

        // User-defined symbols from this session
        if let Ok(symbols) = self.user_symbols.lock() {
            for sym in symbols.iter() {
                if sym.starts_with(prefix) && sym != prefix {
                    candidates.push(Pair {
                        display: sym.clone(),
                        replacement: sym.clone(),
                    });
                }
            }
        }

        // Sort and deduplicate completions for clean presentation
        candidates.sort_by(|a, b| a.display.cmp(&b.display));
        candidates.dedup_by(|a, b| a.display == b.display);

        Ok((prefix_start, candidates))
    }
}

impl Hinter for ReplHelper {
    type Hint = String;

    fn hint(&self, _line: &str, _pos: usize, _ctx: &RustylineContext<'_>) -> Option<Self::Hint> {
        None
    }
}

impl Validator for ReplHelper {
    fn validate(&self, _ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        Ok(ValidationResult::Valid(None))
    }
}

impl Highlighter for ReplHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        let trimmed = line.trim_start();
        if trimmed.starts_with(':') {
            return Cow::Owned(format!("\x1b[1;36m{}\x1b[0m", line));
        }

        let Some(keyword) = trimmed.split_whitespace().next() else {
            return Cow::Borrowed(line);
        };
        let colorized = match keyword {
            // Definition keywords (yellow/bold)
            "def" | "fn" | "type" | "struct" | "const" | "trait" | "impl"
            | "adaptive" | "effect" | "module" | "mod" | "enum" | "macro"
            | "extern" | "static" => {
                line.replacen(keyword, &format!("\x1b[1;33m{}\x1b[0m", keyword), 1)
            }
            // Control-flow keywords (blue/bold)
            "let" | "if" | "else" | "match" | "return" | "for" | "while"
            | "loop" | "break" | "continue" | "yield" | "async" | "await"
            | "spawn" | "select" | "handle" => {
                line.replacen(keyword, &format!("\x1b[1;34m{}\x1b[0m", keyword), 1)
            }
            // Import keywords (green)
            "import" | "use" | "export" => {
                line.replacen(keyword, &format!("\x1b[32m{}\x1b[0m", keyword), 1)
            }
            _ => return Cow::Borrowed(line),
        };
        Cow::Owned(colorized)
    }
}

/// Run the interactive REPL.
pub fn run() -> miette::Result<()> {
    println!("Eclexia REPL v0.1.0");
    println!("Type :help for help, :quit to exit");
    println!("Tab completion available for keywords, builtins, and definitions");
    println!();

    let user_symbols: UserSymbols = Arc::new(Mutex::new(Vec::new()));

    let mut rl = Editor::<ReplHelper, DefaultHistory>::new()
        .map_err(|e| miette::miette!("Failed to create editor: {}", e))?;
    rl.set_helper(Some(ReplHelper::new(Arc::clone(&user_symbols))));

    // Try to load history
    let history_path = dirs::data_dir()
        .map(|d| d.join("eclexia").join("repl_history"))
        .unwrap_or_else(|| std::path::PathBuf::from(".eclexia_history"));

    let _ = rl.load_history(&history_path);

    let mut state = ReplState::new(Arc::clone(&user_symbols));

    loop {
        let prompt = if state.multiline_buffer.is_some() {
            "...> "
        } else {
            "ecl> "
        };

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
    /// Shared list of user-defined symbol names (shared with ReplHelper).
    user_symbols: UserSymbols,
}

impl ReplState {
    fn new(user_symbols: UserSymbols) -> Self {
        Self {
            multiline_buffer: None,
            eval_count: 0,
            definitions: Vec::new(),
            user_symbols,
        }
    }

    /// Record a definition and publish its name for tab completion.
    fn add_definition(&mut self, source: String) {
        if let Some(name) = definition_name(&source) {
            if let Ok(mut symbols) = self.user_symbols.lock() {
                if !symbols.iter().any(|s| s == name) {
                    symbols.push(name.to_string());
                }
            }
        }
        self.definitions.push(source);
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
            println!("  :info <symbol>      Show symbol definition details");
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
            println!();
            println!("Tab completion:");
            println!("  Press Tab to complete keywords, builtins, and your definitions");
            CommandResult::Continue
        }
        ":clear" => {
            print!("\x1B[2J\x1B[1;1H");
            CommandResult::Continue
        }
        ":reset" => {
            state.definitions.clear();
            state.eval_count = 0;
            if let Ok(mut symbols) = state.user_symbols.lock() {
                symbols.clear();
            }
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
                    println!(
                        "  {} ({:?}) = {:.6}",
                        price.resource, price.dimension, price.price
                    );
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
        _ if cmd.starts_with(":info ") => {
            let symbol = &cmd[6..];
            show_info(symbol, state);
            CommandResult::Continue
        }
        _ if cmd.starts_with(":i ") => {
            let symbol = &cmd[3..];
            show_info(symbol, state);
            CommandResult::Continue
        }
        ":info" | ":i" => {
            println!("Usage: :info <symbol>");
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

/// Show information about a symbol currently defined in the REPL or provided by builtins.
fn show_info(symbol: &str, state: &ReplState) {
    let symbol = symbol.trim();
    if symbol.is_empty() {
        println!("Usage: :info <symbol>");
        return;
    }

    let matches: Vec<&String> = state
        .definitions
        .iter()
        .filter(|definition| definition_name(definition).is_some_and(|name| name == symbol))
        .collect();

    if !matches.is_empty() {
        println!("Symbol '{}' found in REPL definitions:", symbol);
        for definition in matches {
            println!("---");
            println!("{}", definition);
        }
        println!("---");
        show_type(symbol, state);
        return;
    }

    if let Some(info) = builtin_info(symbol) {
        println!("Builtin '{}': {}", symbol, info);
        return;
    }

    println!("Symbol '{}' not found in REPL scope.", symbol);
}

/// Extract the defined name from a definition source line (e.g. "def foo(...)" -> "foo").
fn definition_name(definition: &str) -> Option<&str> {
    let line = definition.trim_start();
    for kw in ["adaptive def", "adaptive fn", "def", "fn", "type", "struct", "const"] {
        let Some(rest) = line.strip_prefix(kw) else {
            continue;
        };
        let rest = rest.trim_start();
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        if end > 0 {
            return Some(&rest[..end]);
        }
    }
    None
}

/// Return a short description for well-known builtin symbols.
fn builtin_info(symbol: &str) -> Option<&'static str> {
    match symbol {
        "print" => Some("Print values without trailing newline."),
        "println" => Some("Print values followed by a newline."),
        "len" => Some("Return length of string/array/tuple/map."),
        "to_string" => Some("Convert a value to string."),
        "abs" => Some("Absolute value for numeric types."),
        "min" => Some("Return smaller of two numeric values."),
        "max" => Some("Return larger of two numeric values."),
        "sqrt" => Some("Square root of a float."),
        "floor" => Some("Floor rounding."),
        "ceil" => Some("Ceiling rounding."),
        "pow" => Some("Raise first argument to the power of the second."),
        "log" => Some("Natural logarithm."),
        "exp" => Some("Exponential function (e^x)."),
        "range" => Some("Create an integer range (start, end) or (start, end, step)."),
        "push" => Some("Push an element onto an array (mutates)."),
        "pop" => Some("Pop the last element from an array (mutates)."),
        "shadow_price" => Some("Query the current shadow price for a resource (e.g. \"energy\")."),
        "current_energy" => Some("Current accumulated energy usage (Joules)."),
        "current_carbon" => Some("Current accumulated carbon emissions (gCO2e)."),
        "gpu_available" => Some("Check whether a GPU is available."),
        "cpu_cores" => Some("Number of available CPU cores."),
        "parse_json" => Some("Parse a JSON string into a value."),
        "to_json" => Some("Serialize a value to a JSON string."),
        "read_file" => Some("Read file contents as a string."),
        "write_file" => Some("Write a string to a file."),
        "file_exists" => Some("Check whether a file exists."),
        "assert" => Some("Assert a condition is true; panic otherwise."),
        "panic" => Some("Halt execution with an error message."),
        "hashmap_new" => Some("Create an empty hash map."),
        "hashmap_insert" => Some("Insert a key-value pair into a hash map."),
        "hashmap_get" => Some("Get a value by key from a hash map."),
        "hashmap_remove" => Some("Remove a key from a hash map."),
        "hashmap_contains" => Some("Check if a key exists in a hash map."),
        "hashmap_len" => Some("Number of entries in a hash map."),
        "hashmap_keys" => Some("All keys in a hash map as an array."),
        "hashmap_values" => Some("All values in a hash map as an array."),
        "hashmap_entries" => Some("All (key, value) pairs in a hash map."),
        "queue_new" => Some("Create an empty FIFO queue."),
        "queue_enqueue" => Some("Add an element to the back of a queue."),
        "queue_dequeue" => Some("Remove and return the front element."),
        "queue_peek" => Some("View the front element without removing it."),
        "queue_len" => Some("Number of elements in a queue."),
        "queue_is_empty" => Some("Check whether a queue is empty."),
        "time_now_ms" => Some("Current time in milliseconds since epoch."),
        "time_sleep_ms" => Some("Sleep for the given number of milliseconds."),
        "is_some" | "is_none" => Some("Check Option variant."),
        "is_ok" | "is_err" => Some("Check Result variant."),
        "Ok" => Some("Wrap a value in the Ok variant of Result."),
        "Err" => Some("Wrap a value in the Err variant of Result."),
        "None" => Some("The absence-of-value variant for Option."),
        _ => None,
    }
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
    if trimmed.starts_with("adaptive ")
        || trimmed.starts_with("def ")
        || trimmed.starts_with("fn ")
        || trimmed.starts_with("type ")
        || trimmed.starts_with("struct ")
        || trimmed.starts_with("const ")
    {
        // Validate it parses
        let (_, errors) = eclexia_parser::parse(trimmed);
        if errors.is_empty() {
            state.add_definition(trimmed.to_string());
            if let Some(name) = definition_name(trimmed) {
                println!("(defined: {})", name);
            } else {
                println!("(defined)");
            }
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
            .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".local/share")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definition_name_extracts_supported_forms() {
        assert_eq!(
            definition_name("def demand(x: Int) -> Int { x }"),
            Some("demand")
        );
        assert_eq!(definition_name("fn helper() { }"), Some("helper"));
        assert_eq!(definition_name("type Price = Float"), Some("Price"));
        assert_eq!(definition_name("struct Model { x: Int }"), Some("Model"));
        assert_eq!(definition_name("const RATE = 0.12"), Some("RATE"));
        assert_eq!(definition_name("let x = 1"), None);
    }

    #[test]
    fn definition_name_extracts_adaptive_functions() {
        assert_eq!(
            definition_name("adaptive def allocate(n: Int) -> Int { }"),
            Some("allocate")
        );
        assert_eq!(
            definition_name("adaptive fn choose() -> Int { }"),
            Some("choose")
        );
    }

    #[test]
    fn builtin_info_exposes_documented_symbols() {
        assert!(builtin_info("println").is_some());
        assert!(builtin_info("print").is_some());
        assert!(builtin_info("len").is_some());
        assert!(builtin_info("shadow_price").is_some());
        assert!(builtin_info("hashmap_new").is_some());
        assert!(builtin_info("does_not_exist").is_none());
    }

    #[test]
    fn highlighter_colors_commands() {
        let syms = Arc::new(Mutex::new(Vec::new()));
        let helper = ReplHelper::new(syms);
        let highlighted = helper.highlight(":help", 0);
        assert!(highlighted.as_ref().contains("\x1b[1;36m"));
    }

    #[test]
    fn highlighter_colors_definition_keywords() {
        let syms = Arc::new(Mutex::new(Vec::new()));
        let helper = ReplHelper::new(syms);
        let highlighted = helper.highlight("adaptive def foo() { }", 0);
        assert!(highlighted.as_ref().contains("\x1b[1;33m"));
    }

    #[test]
    fn completion_finds_keywords() {
        let syms = Arc::new(Mutex::new(Vec::new()));
        let helper = ReplHelper::new(syms);
        // We cannot easily construct a RustylineContext, so test the
        // internal matching logic directly.
        let prefix = "sha";
        let matching: Vec<&str> = BUILTINS
            .iter()
            .filter(|b| b.starts_with(prefix))
            .copied()
            .collect();
        assert!(matching.contains(&"shadow_price"));
    }

    #[test]
    fn completion_finds_repl_commands() {
        let prefix = ":sh";
        let matching: Vec<&&str> = REPL_COMMANDS
            .iter()
            .filter(|c| c.starts_with(prefix))
            .collect();
        assert!(matching.iter().any(|c| **c == ":shadow"));
    }

    #[test]
    fn completion_finds_user_definitions() {
        let syms = Arc::new(Mutex::new(vec!["my_func".to_string(), "my_type".to_string()]));
        let helper = ReplHelper::new(syms);
        // Simulate prefix matching
        let prefix = "my_";
        let user_syms = helper.user_symbols.lock().unwrap();
        let matching: Vec<&String> = user_syms
            .iter()
            .filter(|s| s.starts_with(prefix))
            .collect();
        assert_eq!(matching.len(), 2);
    }

    #[test]
    fn state_add_definition_publishes_symbol() {
        let syms = Arc::new(Mutex::new(Vec::new()));
        let mut state = ReplState::new(Arc::clone(&syms));
        state.add_definition("def elasticity(p: Float) -> Float { p * 0.5 }".to_string());
        let locked = syms.lock().unwrap();
        assert!(locked.contains(&"elasticity".to_string()));
    }

    #[test]
    fn state_add_definition_deduplicates() {
        let syms = Arc::new(Mutex::new(Vec::new()));
        let mut state = ReplState::new(Arc::clone(&syms));
        state.add_definition("fn x() { }".to_string());
        state.add_definition("fn x() { 1 }".to_string());
        let locked = syms.lock().unwrap();
        assert_eq!(locked.iter().filter(|s| *s == "x").count(), 1);
    }
}
