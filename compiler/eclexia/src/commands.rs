// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Command implementations for the Eclexia CLI.

use std::path::Path;
use miette::{Context, IntoDiagnostic};

/// Build an Eclexia program.
pub fn build(input: &Path, _output: Option<&Path>, _target: &str) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    // Parse
    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed with {} errors", parse_errors.len()));
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Type checking failed with {} errors", type_errors.len()));
    }

    println!("✓ Build successful");
    println!("  {} items parsed", file.items.len());

    // TODO: Lower to HIR, MIR, and generate code

    Ok(())
}

/// Build and run an Eclexia program.
pub fn run(input: &Path, observe_shadow: bool, carbon_report: bool) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    // Parse
    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed with {} errors", parse_errors.len()));
    }

    if observe_shadow {
        println!("Shadow price observation: λ_energy=1.0, λ_latency=1.0, λ_carbon=1.0");
    }

    // Execute using the interpreter
    println!("Running {}...\n", input.display());

    match eclexia_interp::run(&file) {
        Ok(result) => {
            println!("\nResult: {}", result);

            if carbon_report {
                // TODO: Extract actual resource usage from interpreter
                println!("\n--- Carbon Report ---");
                println!("  Energy used:  (tracked)");
                println!("  Carbon used:  (tracked)");
            }

            Ok(())
        }
        Err(e) => {
            Err(miette::miette!("Runtime error: {}", e))
        }
    }
}

/// Type check a file.
pub fn check(input: &Path) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    let (file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed"));
    }

    let type_errors = eclexia_typeck::check(&file);

    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Type checking failed"));
    }

    println!("✓ No errors found");

    Ok(())
}

/// Format source files.
pub fn fmt(inputs: &[std::path::PathBuf], check: bool) -> miette::Result<()> {
    use eclexia_fmt::Formatter;

    let formatter = Formatter::new();
    let mut has_issues = false;
    let mut changed_files = 0;

    for input in inputs {
        let source = std::fs::read_to_string(input)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

        // Format the source
        let formatted = match formatter.format(&source) {
            Ok(f) => f,
            Err(e) => {
                has_issues = true;
                eprintln!("✗ {}: {}", input.display(), e);
                continue;
            }
        };

        // Check if formatting changed anything
        if formatted != source {
            changed_files += 1;

            if check {
                eprintln!("✗ {} needs formatting", input.display());
                has_issues = true;
            } else {
                // Write formatted code back to file
                std::fs::write(input, &formatted)
                    .into_diagnostic()
                    .wrap_err_with(|| format!("Failed to write {}", input.display()))?;
                println!("✓ Formatted {}", input.display());
            }
        } else {
            if !check {
                println!("✓ {} (no changes needed)", input.display());
            }
        }
    }

    if check && changed_files > 0 {
        Err(miette::miette!(
            "{} file(s) need formatting. Run 'eclexia fmt' to format them.",
            changed_files
        ))
    } else if has_issues {
        Err(miette::miette!("Some files have errors"))
    } else {
        if check {
            println!("✓ All {} files are correctly formatted", inputs.len());
        }
        Ok(())
    }
}

/// Sanitize a project name to prevent path traversal attacks.
fn sanitize_project_name(name: &str) -> miette::Result<&str> {
    // Reject empty names
    if name.is_empty() {
        return Err(miette::miette!("Project name cannot be empty"));
    }

    // Reject absolute paths
    if name.starts_with('/') || name.starts_with('\\') {
        return Err(miette::miette!("Project name cannot be an absolute path"));
    }

    // Reject path traversal sequences
    if name.contains("..") {
        return Err(miette::miette!("Project name cannot contain '..' (path traversal)"));
    }

    // Reject path separators (require simple names)
    if name.contains('/') || name.contains('\\') {
        return Err(miette::miette!("Project name cannot contain path separators"));
    }

    // Reject null bytes
    if name.contains('\0') {
        return Err(miette::miette!("Project name cannot contain null bytes"));
    }

    Ok(name)
}

/// Initialize a new project.
pub fn init(name: Option<&str>) -> miette::Result<()> {
    let project_name = name.unwrap_or("my-eclexia-project");
    let project_name = sanitize_project_name(project_name)?;

    println!("Initializing new Eclexia project: {}", project_name);

    // Create directory structure
    std::fs::create_dir_all(project_name).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/src", project_name)).into_diagnostic()?;

    // Create eclexia.toml
    let config = format!(r#"# SPDX-License-Identifier: MIT
# Eclexia project configuration

[package]
name = "{}"
version = "0.1.0"
edition = "2025"

[dependencies]
# Add your dependencies here

[resources]
default-energy-budget = "1000J"
default-carbon-budget = "100gCO2e"
"#, project_name);

    std::fs::write(format!("{}/eclexia.toml", project_name), config).into_diagnostic()?;

    // Create main.ecl
    let main = r#"// SPDX-License-Identifier: MIT
// Main entry point

def main() -> Unit
    @requires: energy < 1J
{
    println("Hello, Economics-as-Code!")
}
"#;

    std::fs::write(format!("{}/src/main.ecl", project_name), main).into_diagnostic()?;

    println!("✓ Created project in {}/", project_name);
    println!();
    println!("To get started:");
    println!("  cd {}", project_name);
    println!("  eclexia run src/main.ecl");

    Ok(())
}

/// Run tests.
pub fn test(filter: Option<&str>) -> miette::Result<()> {
    use crate::test_runner;

    // Look for test files in src/ and tests/
    let test_patterns = ["src/**/*.ecl", "tests/**/*.ecl"];
    let mut test_files = Vec::new();

    for pattern in test_patterns {
        for entry in glob::glob(pattern).into_diagnostic()? {
            if let Ok(path) = entry {
                test_files.push(path);
            }
        }
    }

    if test_files.is_empty() {
        println!("No test files found.");
        println!("Test files should be placed in src/ or tests/");
        return Ok(());
    }

    let mut total_summary = test_runner::TestSummary::default();

    for test_file in &test_files {
        let source = match std::fs::read_to_string(test_file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read {}: {}", test_file.display(), e);
                continue;
            }
        };

        let (file, errors) = eclexia_parser::parse(&source);
        if !errors.is_empty() {
            eprintln!("Parse errors in {}:", test_file.display());
            for err in &errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            continue;
        }

        // Collect and run tests from this file
        let tests = test_runner::collect_tests(&file);
        if tests.is_empty() {
            continue;
        }

        let summary = test_runner::run_all_tests(&file, filter, true);
        total_summary.passed += summary.passed;
        total_summary.failed += summary.failed;
        total_summary.ignored += summary.ignored;
        total_summary.total_duration_ms += summary.total_duration_ms;
    }

    // Exit with error code if tests failed
    if total_summary.failed > 0 {
        return Err(miette::miette!("{} tests failed", total_summary.failed));
    }

    if total_summary.passed == 0 {
        println!("No tests found.");
        println!("Add #[test] attribute to functions to mark them as tests.");
        return Ok(());
    }

    println!("✓ All {} tests passed", total_summary.passed);
    Ok(())
}

/// Run benchmarks.
pub fn bench(filter: Option<&str>) -> miette::Result<()> {
    use crate::bench_runner;

    // Look for benchmark files in src/ and benches/
    let bench_patterns = ["src/**/*.ecl", "benches/**/*.ecl"];
    let mut bench_files = Vec::new();

    for pattern in bench_patterns {
        for entry in glob::glob(pattern).into_diagnostic()? {
            if let Ok(path) = entry {
                bench_files.push(path);
            }
        }
    }

    if bench_files.is_empty() {
        println!("No benchmark files found.");
        println!("Benchmark files should be placed in src/ or benches/");
        return Ok(());
    }

    let mut total_summary = bench_runner::BenchSummary::default();
    const ITERATIONS: usize = 100; // Number of iterations per benchmark

    for bench_file in &bench_files {
        let source = match std::fs::read_to_string(bench_file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Failed to read {}: {}", bench_file.display(), e);
                continue;
            }
        };

        let (file, errors) = eclexia_parser::parse(&source);
        if !errors.is_empty() {
            eprintln!("Parse errors in {}:", bench_file.display());
            for err in &errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            continue;
        }

        // Collect and run benchmarks from this file
        let benches = bench_runner::collect_benchmarks(&file);
        if benches.is_empty() {
            continue;
        }

        let summary = bench_runner::run_all_benchmarks(&file, filter, ITERATIONS, true);
        total_summary.benchmarks_run += summary.benchmarks_run;
        total_summary.benchmarks_failed += summary.benchmarks_failed;
        total_summary.benchmarks_ignored += summary.benchmarks_ignored;
    }

    // Exit with error code if benchmarks failed
    if total_summary.benchmarks_failed > 0 {
        return Err(miette::miette!("{} benchmarks failed", total_summary.benchmarks_failed));
    }

    if total_summary.benchmarks_run == 0 {
        println!("No benchmarks found.");
        println!("Add #[bench] attribute to functions to mark them as benchmarks.");
        return Ok(());
    }

    println!("✓ All {} benchmarks passed", total_summary.benchmarks_run);
    Ok(())
}

/// Install dependencies from package.toml.
pub fn install() -> miette::Result<()> {
    use crate::package::PackageManifest;
    use crate::package_manager::PackageManager;

    // Load package.toml
    let manifest_path = Path::new("package.toml");
    if !manifest_path.exists() {
        return Err(miette::miette!(
            "No package.toml found in current directory.\nRun 'eclexia init' to create a new project."
        ));
    }

    let manifest_content = std::fs::read_to_string(manifest_path)
        .into_diagnostic()
        .wrap_err("Failed to read package.toml")?;

    let manifest: PackageManifest = toml::from_str(&manifest_content)
        .into_diagnostic()
        .wrap_err("Failed to parse package.toml")?;

    // Initialize package manager and install
    let mut pm = PackageManager::new()
        .map_err(|e| miette::miette!("{}", e))?;

    pm.install(&manifest)
        .map_err(|e| miette::miette!("{}", e))?;

    Ok(())
}

/// Lint source files.
pub fn lint(inputs: &[std::path::PathBuf]) -> miette::Result<()> {
    use eclexia_lint::Linter;

    let linter = Linter::new();
    let mut has_issues = false;
    let mut total_diagnostics = 0;

    for input in inputs {
        let source = std::fs::read_to_string(input)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

        // Parse the file
        let (file, parse_errors) = eclexia_parser::parse(&source);

        if !parse_errors.is_empty() {
            eprintln!("✗ {}: Parse errors prevent linting", input.display());
            has_issues = true;
            continue;
        }

        // Run linter
        let diagnostics = linter.lint(&file, &source);

        if !diagnostics.is_empty() {
            total_diagnostics += diagnostics.len();
            has_issues = true;

            println!("Linting {}:", input.display());
            println!("{}", linter.format_diagnostics(&diagnostics, &source));
        } else {
            println!("✓ {} (no issues)", input.display());
        }
    }

    if has_issues {
        Err(miette::miette!(
            "Found {} lint issue(s) in {} file(s)",
            total_diagnostics,
            inputs.len()
        ))
    } else {
        println!("✓ All {} files passed linting", inputs.len());
        Ok(())
    }
}

/// Debug Eclexia bytecode interactively
pub fn debug(input: &std::path::Path) -> miette::Result<()> {
    use eclexia_debugger::DebugSession;
    use std::io::{self, Write};

    // Read and parse source
    let source = std::fs::read_to_string(input)
        .map_err(|e| miette::miette!("Failed to read {}: {}", input.display(), e))?;

    let (file, parse_errors) = eclexia_parser::parse(&source);
    if !parse_errors.is_empty() {
        return Err(miette::miette!("Cannot debug file with parse errors"));
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);
    if !type_errors.is_empty() {
        return Err(miette::miette!("Cannot debug file with type errors"));
    }

    // Lower to HIR
    let hir_file = eclexia_hir::lower_source_file(&file);

    // Lower to MIR
    let mir_file = eclexia_mir::lower_hir_file(&hir_file);

    // Generate bytecode
    use eclexia_codegen::Backend;
    let mut codegen = eclexia_codegen::BytecodeGenerator::new();
    let module = codegen.generate(&mir_file)
        .map_err(|e| miette::miette!("Code generation failed: {}", e))?;

    // Create VM and debug session
    let vm = eclexia_codegen::VirtualMachine::new(module);
    let mut session = DebugSession::new(vm);

    println!("Eclexia Debugger");
    println!("Type 'help' for commands\n");

    // REPL loop
    loop {
        print!("(eclexia-dbg) ");
        io::stdout().flush().unwrap();

        let mut line = String::new();
        if io::stdin().read_line(&mut line).is_err() {
            break;
        }

        let parts: Vec<&str> = line.trim().split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }

        match parts[0] {
            "help" | "h" => {
                println!("Commands:");
                println!("  help, h           - Show this help");
                println!("  break, b <f> <i>  - Set breakpoint at function index <f>, instruction <i>");
                println!("  delete, d <f> <i> - Remove breakpoint");
                println!("  list, l           - List breakpoints");
                println!("  clear, c          - Clear all breakpoints");
                println!("  step, s           - Step one instruction");
                println!("  continue, r       - Continue execution");
                println!("  stack             - Show stack");
                println!("  locals            - Show local variables");
                println!("  callstack         - Show call stack");
                println!("  resources         - Show resource usage");
                println!("  pos               - Show current position");
                println!("  quit, q           - Exit debugger");
            }
            "break" | "b" => {
                if parts.len() != 3 {
                    println!("Usage: break <function_idx> <instruction_idx>");
                    continue;
                }
                match (parts[1].parse::<usize>(), parts[2].parse::<usize>()) {
                    (Ok(func_idx), Ok(inst_idx)) => {
                        session.set_breakpoint(func_idx, inst_idx);
                        println!("Breakpoint set at {}:{}", func_idx, inst_idx);
                    }
                    _ => println!("Invalid indices"),
                }
            }
            "delete" | "d" => {
                if parts.len() != 3 {
                    println!("Usage: delete <function_idx> <instruction_idx>");
                    continue;
                }
                match (parts[1].parse::<usize>(), parts[2].parse::<usize>()) {
                    (Ok(func_idx), Ok(inst_idx)) => {
                        if session.remove_breakpoint(func_idx, inst_idx) {
                            println!("Breakpoint removed");
                        } else {
                            println!("No breakpoint at {}:{}", func_idx, inst_idx);
                        }
                    }
                    _ => println!("Invalid indices"),
                }
            }
            "list" | "l" => {
                let breakpoints = session.list_breakpoints();
                if breakpoints.is_empty() {
                    println!("No breakpoints set");
                } else {
                    println!("Breakpoints:");
                    for (func_idx, inst_idx) in breakpoints {
                        println!("  {}:{}", func_idx, inst_idx);
                    }
                }
            }
            "clear" | "c" => {
                session.clear_breakpoints();
                println!("All breakpoints cleared");
            }
            "step" | "s" => {
                match session.step() {
                    Ok(()) => println!("{}", session.get_current_instruction()),
                    Err(e) => println!("Error: {}", e),
                }
            }
            "continue" | "r" => {
                match session.continue_execution() {
                    Ok(result) => {
                        use eclexia_debugger::ContinueResult;
                        match result {
                            ContinueResult::Breakpoint(f, i) => {
                                println!("Hit breakpoint at {}:{}", f, i);
                                println!("{}", session.get_current_instruction());
                            }
                            ContinueResult::Finished(val) => {
                                println!("Program finished: {}", val);
                            }
                            ContinueResult::Error(e) => {
                                println!("Error: {}", e);
                            }
                        }
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            "stack" => {
                println!("{}", session.inspect_stack());
            }
            "locals" => {
                println!("{}", session.inspect_locals());
            }
            "callstack" => {
                println!("{}", session.inspect_call_stack());
            }
            "resources" => {
                println!("{}", session.inspect_resources());
            }
            "pos" => {
                if let Some((func_idx, inst_idx)) = session.get_position() {
                    println!("At {}:{}", func_idx, inst_idx);
                    println!("{}", session.get_current_instruction());
                } else {
                    println!("No active frame");
                }
            }
            "quit" | "q" => {
                println!("Exiting debugger");
                break;
            }
            _ => {
                println!("Unknown command: '{}'. Type 'help' for commands.", parts[0]);
            }
        }
    }

    Ok(())
}

/// Generate documentation for Eclexia source files
pub fn doc(inputs: &[std::path::PathBuf], output_dir: &std::path::Path, format: &str) -> miette::Result<()> {
    use eclexia_doc::DocGenerator;

    std::fs::create_dir_all(output_dir)
        .into_diagnostic()
        .wrap_err("Failed to create output directory")?;

    for input in inputs {
        let source = std::fs::read_to_string(input)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

        // Parse the file
        let (file, parse_errors) = eclexia_parser::parse(&source);

        if !parse_errors.is_empty() {
            eprintln!("Warning: {} has parse errors, documentation may be incomplete", input.display());
        }

        // Generate documentation
        let mut generator = DocGenerator::new();
        generator.document_file(&file, &source);

        let module_name = input
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("module");

        let output_content = match format {
            "html" => generator.generate_html(module_name),
            "markdown" | "md" => generator.generate_markdown(module_name),
            _ => {
                return Err(miette::miette!("Unknown format: {}. Use 'html' or 'markdown'", format));
            }
        };

        let ext = if format == "html" { "html" } else { "md" };
        let output_file = output_dir.join(format!("{}.{}", module_name, ext));

        std::fs::write(&output_file, output_content)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to write {}", output_file.display()))?;

        println!("✓ Generated documentation: {}", output_file.display());
    }

    println!("\n✓ Documentation generated in {}/", output_dir.display());

    Ok(())
}
