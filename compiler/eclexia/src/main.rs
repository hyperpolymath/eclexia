// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Eclexia compiler and toolchain CLI.

use clap::{Parser, Subcommand};
use std::path::PathBuf;

mod commands;
mod repl;
mod test_runner;
mod bench_runner;
#[allow(dead_code)]
mod package;
#[allow(dead_code)]
mod resolver;
mod registry;
#[allow(dead_code)]
mod cache;
#[allow(dead_code)]
mod lockfile;
mod package_manager;

#[derive(Parser)]
#[command(name = "eclexia")]
#[command(author, version, about = "Eclexia: Economics-as-Code programming language")]
#[command(propagate_version = true)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Build an Eclexia program
    Build {
        /// Input file
        #[arg(value_name = "FILE")]
        input: PathBuf,

        /// Output file
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Target platform (native, wasm)
        #[arg(short, long, default_value = "native")]
        target: String,
    },

    /// Build and run an Eclexia program
    Run {
        /// Input file
        #[arg(value_name = "FILE")]
        input: PathBuf,

        /// Show shadow prices during execution
        #[arg(long)]
        observe_shadow: bool,

        /// Generate carbon report
        #[arg(long)]
        carbon_report: bool,
    },

    /// Type check a file without building
    Check {
        /// Input file
        #[arg(value_name = "FILE")]
        input: PathBuf,
    },

    /// Format Eclexia source code
    Fmt {
        /// Input file(s)
        #[arg(value_name = "FILE")]
        input: Vec<PathBuf>,

        /// Check formatting without modifying files
        #[arg(long)]
        check: bool,
    },

    /// Run the interactive REPL
    Repl,

    /// Initialize a new Eclexia project
    Init {
        /// Project name
        #[arg(value_name = "NAME")]
        name: Option<String>,
    },

    /// Create a new Eclexia project from a template
    New {
        /// Project name
        #[arg(value_name = "NAME")]
        name: String,

        /// Project template
        #[arg(short, long, default_value = "bin")]
        template: String,
    },

    /// Run tests
    Test {
        /// Test filter pattern
        #[arg(value_name = "FILTER")]
        filter: Option<String>,
    },

    /// Run benchmarks
    Bench {
        /// Benchmark filter pattern
        #[arg(value_name = "FILTER")]
        filter: Option<String>,
    },

    /// Lint Eclexia source code
    Lint {
        /// Input file(s)
        #[arg(value_name = "FILE")]
        input: Vec<PathBuf>,
    },

    /// Debug Eclexia bytecode
    Debug {
        /// Input file
        #[arg(value_name = "FILE")]
        input: PathBuf,
    },

    /// Generate documentation
    Doc {
        /// Input file(s)
        #[arg(value_name = "FILE")]
        input: Vec<PathBuf>,

        /// Output directory
        #[arg(short, long, default_value = "docs")]
        output: PathBuf,

        /// Output format
        #[arg(short, long, default_value = "html")]
        format: String,
    },

    /// Install dependencies from package.toml
    Install,

    /// Watch for file changes and rebuild incrementally
    Watch {
        /// Input file or directory to watch
        #[arg(value_name = "PATH", default_value = ".")]
        path: PathBuf,

        /// Debounce delay in milliseconds
        #[arg(long, default_value = "100")]
        debounce: u64,
    },

    /// Disassemble compiled bytecode
    Disasm {
        /// Input file
        #[arg(value_name = "FILE")]
        input: PathBuf,
    },
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Build { input, output, target } => {
            commands::build(&input, output.as_deref(), &target)?;
        }
        Commands::Run { input, observe_shadow, carbon_report } => {
            commands::run(&input, observe_shadow, carbon_report)?;
        }
        Commands::Check { input } => {
            commands::check(&input)?;
        }
        Commands::Fmt { input, check } => {
            commands::fmt(&input, check)?;
        }
        Commands::Repl => {
            repl::run()?;
        }
        Commands::Init { name } => {
            commands::init(name.as_deref())?;
        }
        Commands::New { name, template } => {
            commands::new_project(&name, &template)?;
        }
        Commands::Test { filter } => {
            commands::test(filter.as_deref())?;
        }
        Commands::Bench { filter } => {
            commands::bench(filter.as_deref())?;
        }
        Commands::Lint { input } => {
            commands::lint(&input)?;
        }
        Commands::Debug { input } => {
            commands::debug(&input)?;
        }
        Commands::Doc { input, output, format } => {
            commands::doc(&input, &output, &format)?;
        }
        Commands::Install => {
            commands::install()?;
        }
        Commands::Watch { path, debounce } => {
            commands::watch(&path, debounce)?;
        }
        Commands::Disasm { input } => {
            commands::disasm(&input)?;
        }
    }

    Ok(())
}
