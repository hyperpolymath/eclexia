// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Command implementations for the Eclexia CLI.

use eclexia_runtime::{HealthServer, PowerMetrics, Runtime};
use miette::{Context, IntoDiagnostic};
use std::path::Path;
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Build an Eclexia program.
pub fn build(
    input: &Path,
    _output: Option<&Path>,
    _target: &str,
    analyze: bool,
) -> miette::Result<()> {
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
        return Err(miette::miette!(
            "Parsing failed with {} errors",
            parse_errors.len()
        ));
    }

    // Module resolution + interface generation (wiring eclexia-modules into CLI)
    compile_module_graph(input)?;

    // Lower to HIR
    let hir_file = eclexia_hir::lower_source_file(&file);

    // Lower to MIR
    let mir_file = eclexia_mir::lower_hir_file(&hir_file);

    // Run analysis passes if requested
    if analyze {
        run_mir_analysis(&mir_file, &file, &source);
    }

    // Select backend based on target
    use eclexia_codegen::Backend;

    match _target {
        "wasm" => {
            // WASM backend: generate real .wasm binary
            let mut wasm_backend = eclexia_wasm::WasmBackend::new();
            let wasm_module = wasm_backend
                .generate(&mir_file)
                .map_err(|e| miette::miette!("WASM code generation failed: {}", e))?;

            println!("✓ Build successful (target: wasm)");
            println!("  {} items parsed", file.items.len());
            println!("  {} functions compiled", wasm_module.functions.len());
            println!("  {} imports required", wasm_module.imports.len());
            println!("  {} exports", wasm_module.exports.len());
            println!("  {} bytes binary size", wasm_module.binary_size);

            let out_path = _output
                .map(|p| p.to_path_buf())
                .unwrap_or_else(|| input.with_extension("wasm"));
            std::fs::write(&out_path, wasm_module.to_bytes())
                .into_diagnostic()
                .wrap_err_with(|| format!("Failed to write WASM to {}", out_path.display()))?;
            println!("  WASM module written to {}", out_path.display());
        }
        "cranelift" => {
            // Cranelift native backend
            let mut cl_backend = eclexia_cranelift::CraneliftBackend::host();
            let native_module = cl_backend
                .generate(&mir_file)
                .map_err(|e| miette::miette!("Cranelift code generation failed: {}", e))?;

            let real_count = native_module
                .functions
                .iter()
                .filter(|f| f.is_real_codegen)
                .count();
            let est_count = native_module.functions.len() - real_count;

            println!(
                "✓ Build successful (target: cranelift, {})",
                native_module.target
            );
            println!("  {} items parsed", file.items.len());
            println!(
                "  {} functions compiled ({} real native, {} estimated)",
                native_module.functions.len(),
                real_count,
                est_count
            );
            println!("  {} bytes total code size", native_module.total_code_size);

            for func in &native_module.functions {
                let tag = if func.is_real_codegen {
                    "native"
                } else {
                    "est"
                };
                println!("    {} ({}, {} bytes)", func.name, tag, func.code_size);
            }
        }
        "llvm" => {
            let mut llvm_backend = eclexia_llvm::LlvmBackend::new();
            let llvm_module = llvm_backend
                .generate(&mir_file)
                .map_err(|e| miette::miette!("LLVM code generation failed: {}", e))?;

            let output_base = _output
                .map(|path| path.with_extension(""))
                .unwrap_or_else(|| input.with_extension(""));
            let ll_path = output_base.with_extension("ll");
            let obj_path = output_base.with_extension("o");

            if let Some(parent) = ll_path.parent() {
                std::fs::create_dir_all(parent)
                    .into_diagnostic()
                    .wrap_err_with(|| format!("Failed to create directory {}", parent.display()))?;
            }

            llvm_module
                .write_to_file(&ll_path)
                .into_diagnostic()
                .wrap_err_with(|| format!("Failed to write LLVM IR to {}", ll_path.display()))?;
            println!("  LLVM IR written to {}", ll_path.display());

            let compile_start = Instant::now();
            let llc_result =
                llvm_module.compile_with_llc(&ll_path, &obj_path, llvm_module.opt_level);
            let compile_duration = compile_start.elapsed();

            match llc_result {
                Ok(()) => println!(
                    "  Object file written to {} (llc took {} ms)",
                    obj_path.display(),
                    compile_duration.as_millis()
                ),
                Err(err) => {
                    return Err(miette::miette!(
                        "llc failed ({}) after {} ms. LLVM IR is at {}. Install LLVM 17 or run `llc {}` manually.",
                        err,
                        compile_duration.as_millis(),
                        ll_path.display(),
                        ll_path.display()
                    ));
                }
            }

            println!("✓ Build successful (target: llvm)");
            println!("  {} items parsed", file.items.len());
            println!("  {} functions analyzed", llvm_module.functions.len());
            println!("  Optimization: {}", llvm_module.opt_level);
            println!(
                "  Estimated code size: {} bytes",
                llvm_module.estimated_code_size
            );

            for func in &llvm_module.functions {
                println!(
                    "    {} (~{} bytes estimated)",
                    func.name, func.estimated_size
                );
            }
        }
        _ => {
            // Default: bytecode backend ("native" or anything else)
            let mut codegen = eclexia_codegen::BytecodeGenerator::new();
            let module = codegen
                .generate(&mir_file)
                .map_err(|e| miette::miette!("Code generation failed: {}", e))?;

            println!("✓ Build successful");
            println!("  {} items parsed", file.items.len());
            println!("  {} functions compiled", module.functions.len());

            if let Some(output) = _output {
                if eclexia_codegen::bytecode::BytecodeModule::is_eclb_path(output) {
                    // Binary .eclb format
                    module
                        .write_eclb(output)
                        .map_err(|e| miette::miette!("{}", e))?;
                    println!("  Bytecode written to {} (.eclb binary)", output.display());
                } else {
                    // JSON format for .json or any other extension
                    let json = serde_json::to_vec_pretty(&module)
                        .map_err(|e| miette::miette!("Failed to serialize bytecode: {}", e))?;
                    std::fs::write(output, &json)
                        .into_diagnostic()
                        .wrap_err_with(|| {
                            format!("Failed to write bytecode to {}", output.display())
                        })?;
                    println!("  Bytecode written to {} (JSON)", output.display());
                }
            }
        }
    }

    Ok(())
}

/// Build with watch mode: rebuild on file changes.
pub fn build_watch(
    input: &Path,
    output: Option<&Path>,
    target: &str,
    analyze: bool,
) -> miette::Result<()> {
    use eclexia_tiered::watch::WatchConfig;
    use std::sync::mpsc;

    let watch_config = WatchConfig::new(input.parent().unwrap_or(Path::new(".")).to_path_buf());

    println!(
        "Watch mode: monitoring {} for changes (debounce: {}ms)",
        watch_config.root.display(),
        watch_config.debounce.as_millis()
    );
    println!("Press Ctrl+C to stop.\n");

    // Initial build
    println!("Initial build...");
    if let Err(e) = build(input, output, target, analyze) {
        eprintln!("Build failed: {}", e);
    }

    println!("\n--- Watching for changes ---\n");

    // Set up file watcher
    let (tx, rx) = mpsc::channel::<notify::Event>();

    let mut watcher =
        notify::recommended_watcher(move |res: Result<notify::Event, notify::Error>| {
            if let Ok(event) = res {
                if matches!(
                    event.kind,
                    notify::EventKind::Modify(_)
                        | notify::EventKind::Create(_)
                        | notify::EventKind::Remove(_)
                ) {
                    let _ = tx.send(event);
                }
            }
        })
        .into_diagnostic()
        .wrap_err("Failed to create file watcher")?;

    use notify::Watcher;
    watcher
        .watch(&watch_config.root, notify::RecursiveMode::Recursive)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to watch {}", watch_config.root.display()))?;

    // Event loop with debouncing
    loop {
        let first_event = rx.recv().into_diagnostic()?;
        let mut changed: std::collections::HashSet<std::path::PathBuf> =
            std::collections::HashSet::new();
        for p in &first_event.paths {
            if watch_config.should_watch(p) {
                changed.insert(p.clone());
            }
        }

        // Debounce window
        let deadline = std::time::Instant::now() + watch_config.debounce;
        loop {
            match rx.recv_timeout(deadline.saturating_duration_since(std::time::Instant::now())) {
                Ok(event) => {
                    for p in &event.paths {
                        if watch_config.should_watch(p) {
                            changed.insert(p.clone());
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => break,
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(miette::miette!("File watcher disconnected"));
                }
            }
        }

        if !changed.is_empty() {
            println!("\n{} file(s) changed, rebuilding...", changed.len());
            let start = std::time::Instant::now();

            match build(input, output, target, analyze) {
                Ok(()) => {
                    println!("✓ Build successful ({:.2}s)", start.elapsed().as_secs_f64());
                }
                Err(e) => {
                    eprintln!("✗ Build failed: {}", e);
                }
            }
            println!();
        }
    }
}

fn find_project_root(input: &Path) -> std::path::PathBuf {
    for ancestor in input.ancestors() {
        if ancestor.join("package.toml").is_file() || ancestor.join("Cargo.toml").is_file() {
            return ancestor.to_path_buf();
        }
    }

    input
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf()
}

fn find_stdlib_root(root: &Path) -> Option<std::path::PathBuf> {
    for ancestor in root.ancestors() {
        let candidate = ancestor.join("stdlib");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    None
}

fn module_id_for_path(root: &Path, path: &Path) -> eclexia_modules::ModuleId {
    let rel = path.strip_prefix(root).unwrap_or(path);
    eclexia_modules::ModuleId::from_file_path(rel).unwrap_or_else(|| {
        let raw = rel
            .with_extension("")
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, ".");
        eclexia_modules::ModuleId::new(raw)
    })
}

fn compile_module_graph(input: &Path) -> miette::Result<()> {
    use eclexia_modules::dep_graph::DependencyGraph;
    use eclexia_modules::interface::ModuleInterface;
    use eclexia_modules::parallel::{
        CompilationError, CompilationUnit, ErrorSeverity, ParallelCompilationError,
        ParallelScheduler,
    };
    use eclexia_modules::{extract_imports, ModuleResolver};
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::sync::Arc;

    let root = find_project_root(input);
    let mut resolver = ModuleResolver::new(root.clone());
    if let Some(stdlib) = find_stdlib_root(&root) {
        resolver.add_search_path(stdlib);
    }

    let entry_id = module_id_for_path(&root, input);
    let mut graph = DependencyGraph::new();
    let mut module_paths: HashMap<eclexia_modules::ModuleId, std::path::PathBuf> = HashMap::new();
    let mut queue = VecDeque::new();
    let mut visited: HashSet<eclexia_modules::ModuleId> = HashSet::new();

    graph.add_module(entry_id.clone());
    module_paths.insert(entry_id.clone(), input.to_path_buf());
    queue.push_back(entry_id.clone());

    while let Some(module_id) = queue.pop_front() {
        if visited.contains(&module_id) {
            continue;
        }
        visited.insert(module_id.clone());

        let path = if let Some(path) = module_paths.get(&module_id) {
            path.clone()
        } else {
            resolver
                .resolve(&module_id)
                .map_err(|e| miette::miette!("Module resolution failed: {}", e))?
        };

        let source = std::fs::read_to_string(&path)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", path.display()))?;

        let (file, parse_errors) = eclexia_parser::parse(&source);
        if !parse_errors.is_empty() {
            eprintln!("Parse errors in {}:", path.display());
            for err in &parse_errors {
                eprintln!("  {}", err.format_with_source(&source));
            }
            return Err(miette::miette!(
                "Parsing failed for {} with {} errors",
                path.display(),
                parse_errors.len()
            ));
        }

        let imports = extract_imports(&file);
        for import in imports {
            graph.add_dependency(&module_id, &import);
            if !module_paths.contains_key(&import) {
                let import_path = resolver
                    .resolve(&import)
                    .map_err(|e| miette::miette!("Module resolution failed: {}", e))?;
                module_paths.insert(import.clone(), import_path);
            }
            queue.push_back(import);
        }
    }

    let Some(_order) = graph.topological_order() else {
        return Err(miette::miette!("Module dependency cycle detected"));
    };

    let build_dir = root.join("target").join("eclexia").join("interfaces");
    std::fs::create_dir_all(&build_dir)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to create {}", build_dir.display()))?;

    let module_paths = Arc::new(module_paths);
    let build_dir = Arc::new(build_dir);

    let scheduler = ParallelScheduler::new();
    let results = match scheduler.compile_all(&graph, |module_id| {
        let mut errors = Vec::new();
        let path = match module_paths.get(module_id) {
            Some(path) => path.clone(),
            None => {
                errors.push(CompilationError {
                    module_id: module_id.clone(),
                    message: "module path not resolved".to_string(),
                    severity: ErrorSeverity::Error,
                });
                return CompilationUnit {
                    module_id: module_id.clone(),
                    interface: ModuleInterface::new(module_id),
                    errors,
                };
            }
        };

        let iface_path = ModuleInterface::interface_path(module_id, &build_dir);
        let dependencies = graph.dependencies(module_id);
        if interface_is_fresh(&path, &iface_path, &dependencies, &build_dir) {
            if let Ok(interface) = ModuleInterface::read_from_file(&iface_path) {
                return CompilationUnit {
                    module_id: module_id.clone(),
                    interface,
                    errors,
                };
            }
        }

        let source = match std::fs::read_to_string(&path) {
            Ok(source) => source,
            Err(err) => {
                errors.push(CompilationError {
                    module_id: module_id.clone(),
                    message: format!("failed to read {}: {}", path.display(), err),
                    severity: ErrorSeverity::Error,
                });
                return CompilationUnit {
                    module_id: module_id.clone(),
                    interface: ModuleInterface::new(module_id),
                    errors,
                };
            }
        };

        let (file, parse_errors) = eclexia_parser::parse(&source);
        if !parse_errors.is_empty() {
            for err in &parse_errors {
                errors.push(CompilationError {
                    module_id: module_id.clone(),
                    message: err.format_with_source(&source),
                    severity: ErrorSeverity::Error,
                });
            }
        }

        let mut dependency_interfaces = Vec::new();
        if parse_errors.is_empty() {
            for dep in &dependencies {
                let dep_iface = ModuleInterface::interface_path(dep, &build_dir);
                match ModuleInterface::read_from_file(&dep_iface) {
                    Ok(interface) => dependency_interfaces.push(interface),
                    Err(err) => {
                        errors.push(CompilationError {
                            module_id: module_id.clone(),
                            message: format!(
                                "failed to read interface {}: {}",
                                dep_iface.display(),
                                err
                            ),
                            severity: ErrorSeverity::Error,
                        });
                    }
                }
            }
        }

        let type_errors = if parse_errors.is_empty() && errors.is_empty() {
            type_check_with_interfaces(&file, &dependency_interfaces)
        } else {
            Vec::new()
        };
        for err in &type_errors {
            errors.push(CompilationError {
                module_id: module_id.clone(),
                message: err.format_with_source(&source),
                severity: ErrorSeverity::Error,
            });
        }

        let interface = ModuleInterface::from_ast(module_id, &file);
        if errors.is_empty() {
            let iface_path = ModuleInterface::interface_path(module_id, &build_dir);
            if let Some(parent) = iface_path.parent() {
                if let Err(err) = std::fs::create_dir_all(parent) {
                    errors.push(CompilationError {
                        module_id: module_id.clone(),
                        message: format!(
                            "failed to create module interface directory {}: {}",
                            parent.display(),
                            err
                        ),
                        severity: ErrorSeverity::Error,
                    });
                }
            }
            if errors.is_empty() {
                if let Err(err) = interface.write_to_file(&iface_path) {
                    errors.push(CompilationError {
                        module_id: module_id.clone(),
                        message: format!("failed to write {}: {}", iface_path.display(), err),
                        severity: ErrorSeverity::Error,
                    });
                }
            }
        }

        CompilationUnit {
            module_id: module_id.clone(),
            interface,
            errors,
        }
    }) {
        Ok(results) => results,
        Err(ParallelCompilationError::CompilationFailed { results }) => {
            report_module_errors(&results);
            return Err(miette::miette!("Module compilation failed"));
        }
        Err(ParallelCompilationError::CyclicDependency) => {
            return Err(miette::miette!("Module dependency cycle detected"));
        }
        Err(ParallelCompilationError::ThreadPoolError(message)) => {
            return Err(miette::miette!("Parallel compilation failed: {}", message));
        }
    };

    println!(
        "  Modules compiled: {} (interfaces in {})",
        results.len(),
        build_dir.display()
    );

    Ok(())
}

fn interface_is_fresh(
    source_path: &Path,
    iface_path: &Path,
    deps: &[&eclexia_modules::ModuleId],
    build_dir: &Path,
) -> bool {
    let iface_mtime = match std::fs::metadata(iface_path).and_then(|m| m.modified()) {
        Ok(time) => time,
        Err(_) => return false,
    };
    let source_mtime = match std::fs::metadata(source_path).and_then(|m| m.modified()) {
        Ok(time) => time,
        Err(_) => return false,
    };

    if iface_mtime < source_mtime {
        return false;
    }

    for dep in deps {
        let dep_iface = eclexia_modules::interface::ModuleInterface::interface_path(dep, build_dir);
        let dep_mtime = match std::fs::metadata(&dep_iface).and_then(|m| m.modified()) {
            Ok(time) => time,
            Err(_) => return false,
        };
        if dep_mtime > iface_mtime {
            return false;
        }
    }

    true
}

fn type_check_with_interfaces(
    file: &eclexia_ast::SourceFile,
    interfaces: &[eclexia_modules::interface::ModuleInterface],
) -> Vec<eclexia_typeck::TypeError> {
    let mut checker = eclexia_typeck::TypeChecker::new(file);
    apply_module_interfaces(&mut checker, interfaces);
    checker.check_all()
}

fn apply_module_interfaces(
    checker: &mut eclexia_typeck::TypeChecker,
    interfaces: &[eclexia_modules::interface::ModuleInterface],
) {
    use eclexia_ast::types::{Ty, TypeVar};
    use rustc_hash::FxHashMap;

    for iface in interfaces {
        let mut mapping: FxHashMap<TypeVar, TypeVar> = FxHashMap::default();

        for func in &iface.functions {
            let raw_ty = Ty::Function {
                params: func.params.iter().map(|p| p.ty.clone()).collect(),
                ret: Box::new(func.return_type.clone()),
            };
            let func_ty = freshen_type_with_map(checker, &raw_ty, &mut mapping);
            checker
                .env_mut()
                .insert_mono(smol_str::SmolStr::new(func.name.clone()), func_ty);
        }

        for typedef in &iface.types {
            match &typedef.kind {
                eclexia_modules::interface::TypeDefKind::Struct { fields } => {
                    let field_info = fields
                        .iter()
                        .map(|f| {
                            (
                                smol_str::SmolStr::new(f.name.clone()),
                                freshen_type_with_map(checker, &f.ty, &mut mapping),
                            )
                        })
                        .collect();
                    checker
                        .env_mut()
                        .register_struct(smol_str::SmolStr::new(typedef.name.clone()), field_info);
                }
                eclexia_modules::interface::TypeDefKind::Enum { variants } => {
                    let enum_name = smol_str::SmolStr::new(typedef.name.clone());
                    for variant in variants {
                        if variant.fields.is_empty() {
                            checker.env_mut().insert_mono(
                                smol_str::SmolStr::new(variant.name.clone()),
                                Ty::Named {
                                    name: enum_name.clone(),
                                    args: vec![],
                                },
                            );
                        } else {
                            let params = variant
                                .fields
                                .iter()
                                .map(|f| freshen_type_with_map(checker, &f.ty, &mut mapping))
                                .collect();
                            let ctor_ty = Ty::Function {
                                params,
                                ret: Box::new(Ty::Named {
                                    name: enum_name.clone(),
                                    args: vec![],
                                }),
                            };
                            checker
                                .env_mut()
                                .insert_mono(smol_str::SmolStr::new(variant.name.clone()), ctor_ty);
                        }
                    }
                }
                eclexia_modules::interface::TypeDefKind::Alias { target } => {
                    let alias_ty = freshen_type_with_map(checker, target, &mut mapping);
                    checker
                        .env_mut()
                        .insert_mono(smol_str::SmolStr::new(typedef.name.clone()), alias_ty);
                }
            }
        }

        for tr in &iface.traits {
            let methods = tr
                .methods
                .iter()
                .map(|m| {
                    let raw_ty = Ty::Function {
                        params: m.params.iter().map(|p| p.ty.clone()).collect(),
                        ret: Box::new(m.return_type.clone()),
                    };
                    let method_ty = freshen_type_with_map(checker, &raw_ty, &mut mapping);
                    (smol_str::SmolStr::new(m.name.clone()), method_ty)
                })
                .collect();
            checker
                .env_mut()
                .register_trait(smol_str::SmolStr::new(tr.name.clone()), methods);
        }

        for constant in &iface.constants {
            let const_ty = freshen_type_with_map(checker, &constant.ty, &mut mapping);
            checker
                .env_mut()
                .insert_mono(smol_str::SmolStr::new(constant.name.clone()), const_ty);
        }
    }
}

fn freshen_type_with_map(
    checker: &mut eclexia_typeck::TypeChecker,
    ty: &eclexia_ast::types::Ty,
    mapping: &mut rustc_hash::FxHashMap<eclexia_ast::types::TypeVar, eclexia_ast::types::TypeVar>,
) -> eclexia_ast::types::Ty {
    use eclexia_ast::types::Ty;

    match ty {
        Ty::Primitive(p) => Ty::Primitive(*p),
        Ty::Named { name, args } => Ty::Named {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| freshen_type_with_map(checker, arg, mapping))
                .collect(),
        },
        Ty::Function { params, ret } => Ty::Function {
            params: params
                .iter()
                .map(|p| freshen_type_with_map(checker, p, mapping))
                .collect(),
            ret: Box::new(freshen_type_with_map(checker, ret, mapping)),
        },
        Ty::Tuple(elems) => Ty::Tuple(
            elems
                .iter()
                .map(|elem| freshen_type_with_map(checker, elem, mapping))
                .collect(),
        ),
        Ty::Array { elem, size } => Ty::Array {
            elem: Box::new(freshen_type_with_map(checker, elem, mapping)),
            size: *size,
        },
        Ty::Resource { base, dimension } => Ty::Resource {
            base: *base,
            dimension: *dimension,
        },
        Ty::Var(var) => {
            let entry = mapping.entry(*var).or_insert_with(|| {
                let fresh = checker.fresh_var();
                if let Ty::Var(new_var) = fresh {
                    new_var
                } else {
                    eclexia_ast::types::TypeVar::new(0)
                }
            });
            Ty::Var(*entry)
        }
        Ty::ForAll { vars, body } => Ty::ForAll {
            vars: vars.clone(),
            body: Box::new(freshen_type_with_map(checker, body, mapping)),
        },
        Ty::Error => Ty::Error,
        Ty::Never => Ty::Never,
    }
}

fn report_module_errors(results: &[eclexia_modules::parallel::CompilationUnit]) {
    eprintln!("Module compilation errors:");
    for unit in results {
        for err in &unit.errors {
            eprintln!("  {}: {}", unit.module_id, err.message);
        }
    }
}

/// Run MIR-level analysis passes: constant folding, resource analysis, budget verification.
fn run_mir_analysis(mir: &eclexia_mir::MirFile, ast: &eclexia_ast::SourceFile, source: &str) {
    println!("\n--- MIR Analysis ---");

    // Compile-time constant folding analysis
    let foldable = eclexia_comptime::const_fold::analyze_foldable(mir);
    println!("  Constant folding: {} foldable instruction(s)", foldable);

    // Compile-time resource budget verification
    let comptime_verdicts = eclexia_comptime::resource_verify::verify_resource_budgets(mir);
    if !comptime_verdicts.is_empty() {
        println!("  Compile-time resource verification:");
        for verdict in &comptime_verdicts {
            match verdict {
                eclexia_comptime::ResourceVerification::Proved {
                    function, resource, ..
                } => {
                    println!("    ✓ {}.{} provably within budget", function, resource);
                }
                eclexia_comptime::ResourceVerification::Violated {
                    function,
                    resource,
                    estimated_usage,
                    budget,
                    ..
                } => {
                    println!(
                        "    ✗ {}.{} VIOLATED: estimated {:.2} > budget {:.2}",
                        function, resource, estimated_usage, budget
                    );
                }
                eclexia_comptime::ResourceVerification::Inconclusive {
                    function,
                    resource,
                    reason,
                } => {
                    println!("    ? {}.{} inconclusive: {}", function, resource, reason);
                }
            }
        }
    }

    // Abstract interpretation resource bounds
    let resource_analyses = eclexia_absinterp::resource::analyze_resources(mir);
    let has_resources = resource_analyses
        .iter()
        .any(|a| !a.resource_bounds.is_empty());
    if has_resources {
        println!("  Resource bounds (abstract interpretation):");
        for analysis in &resource_analyses {
            if analysis.resource_bounds.is_empty() {
                continue;
            }
            println!("    fn {}:", analysis.function);
            for bound in &analysis.resource_bounds {
                if bound.max_usage.is_infinite() {
                    println!("      {}: [{:.2}, +inf)", bound.resource, bound.min_usage);
                } else {
                    println!(
                        "      {}: [{:.2}, {:.2}]",
                        bound.resource, bound.min_usage, bound.max_usage
                    );
                }
            }
        }
    }

    // Budget verdicts from abstract interpretation
    let budget_verdicts = eclexia_absinterp::resource::verify_budgets(mir);
    if !budget_verdicts.is_empty() {
        println!("  Budget verdicts:");
        for (func, resource, verdict) in &budget_verdicts {
            match verdict {
                eclexia_absinterp::BudgetVerdict::Proved => {
                    println!("    ✓ {}.{} provably within budget", func, resource);
                }
                eclexia_absinterp::BudgetVerdict::Disproved { min_usage, limit } => {
                    println!(
                        "    ✗ {}.{} EXCEEDED: min {:.2} > limit {:.2}",
                        func, resource, min_usage, limit
                    );
                }
                eclexia_absinterp::BudgetVerdict::Unknown => {
                    println!("    ? {}.{} inconclusive", func, resource);
                }
            }
        }
    }

    // Binding-time analysis (specialization opportunities)
    let mut specializable = 0usize;
    let mut total_adaptive = 0usize;
    for func in &mir.functions {
        if func.is_adaptive {
            total_adaptive += 1;
            let param_bts = vec![eclexia_specialize::BindingTime::Dynamic; func.params.len()];
            let env = eclexia_specialize::binding_time::analyze_function(func, mir, &param_bts);
            if eclexia_specialize::binding_time::constraints_are_static(func, mir, &env) {
                specializable += 1;
            }
        }
    }
    if total_adaptive > 0 {
        println!(
            "  Binding-time analysis: {}/{} adaptive function(s) specializable",
            specializable, total_adaptive
        );
    }

    // Effect signature analysis
    let mut effect_registry = eclexia_effects::evidence::EffectRegistry::new();
    for item in &ast.items {
        if let eclexia_ast::Item::EffectDecl(decl) = item {
            let sig = eclexia_effects::effect_signature_from_decl(decl);
            effect_registry.register(sig);
        }
    }
    if !effect_registry.is_empty() {
        println!(
            "  Effect signatures: {} effect(s) registered",
            effect_registry.len()
        );
    }

    // Module import analysis with dependency graph statistics
    let imports = eclexia_modules::extract_imports(ast);
    if !imports.is_empty() {
        println!("  Module imports: {} import(s) detected", imports.len());

        // Build dependency graph for analysis
        use eclexia_modules::dep_graph::DependencyGraph;
        let mut dep_graph = DependencyGraph::new();
        let current_module = eclexia_modules::ModuleId::new("current".to_string());
        dep_graph.add_module(current_module.clone());

        for import in &imports {
            dep_graph.add_module(import.clone());
            dep_graph.add_dependency(&current_module, import);
            println!("    - {}", import.path);
        }

        // Report graph statistics
        let total_modules = dep_graph.len();
        println!("    Graph: {} module(s) total", total_modules);
        println!(
            "    Edges: {} dependency relation(s)",
            dep_graph.edge_count()
        );

        // Check for cycles
        if dep_graph.topological_order().is_none() {
            println!("    ⚠  Potential dependency cycle detected");
        }

        // Report leaf and root modules
        let leaf_count = dep_graph.leaf_modules().len();
        let root_count = dep_graph.root_modules().len();
        if leaf_count > 0 {
            println!("    Leaf modules (no dependencies): {}", leaf_count);
        }
        if root_count > 0 {
            println!("    Root modules (not imported): {}", root_count);
        }
    }

    // Tiered execution analysis
    {
        let mut tier_mgr = eclexia_tiered::tier::TierManager::new();

        // Estimate hotness: functions with more instructions or recursion are hotter
        for func in &mir.functions {
            let instr_count: usize = func
                .basic_blocks
                .iter()
                .map(|(_, bb)| bb.instructions.len())
                .sum();

            // Heuristic: more instructions → more likely hot
            let estimated_calls = if func.is_adaptive {
                200
            } else if instr_count > 50 {
                1500
            } else if instr_count > 20 {
                150
            } else {
                5
            };

            for _ in 0..estimated_calls {
                tier_mgr.record_call(&func.name);
            }
        }

        // Report tier distribution
        let mut has_tiers = false;
        for tier in [
            eclexia_tiered::tier::Tier::Interpreter,
            eclexia_tiered::tier::Tier::Bytecode,
            eclexia_tiered::tier::Tier::Cranelift,
            eclexia_tiered::tier::Tier::Llvm,
        ] {
            let funcs_at_tier = tier_mgr.functions_at_tier(tier);
            if !funcs_at_tier.is_empty() {
                if !has_tiers {
                    println!("  Tiered execution (estimated):");
                    has_tiers = true;
                }
                println!("    {}: {} function(s)", tier, funcs_at_tier.len());
            }
        }
    }

    // Incremental compilation readiness (salsa database)
    {
        let db = eclexia_db::CompilerDatabase::new();
        let source_text = source.to_string();
        let source = eclexia_db::SourceFile::new(&db, source_text);
        let all_diags = eclexia_db::queries::all_diagnostics(&db, source);
        let errors: Vec<_> = all_diags
            .iter()
            .filter(|d| d.severity == eclexia_db::DiagnosticSeverity::Error)
            .collect();
        let warnings: Vec<_> = all_diags
            .iter()
            .filter(|d| d.severity == eclexia_db::DiagnosticSeverity::Warning)
            .collect();
        if !all_diags.is_empty() {
            println!(
                "  Incremental compilation (salsa): {} error(s), {} warning(s)",
                errors.len(),
                warnings.len()
            );
        }
    }

    if comptime_verdicts.is_empty()
        && !has_resources
        && budget_verdicts.is_empty()
        && total_adaptive == 0
        && effect_registry.is_empty()
        && imports.is_empty()
    {
        println!("  No resource constraints to analyze");
    }

    println!();
}

/// Build and run an Eclexia program (source .ecl or bytecode .eclb).
pub fn run(input: &Path, observe_shadow: bool, carbon_report: bool) -> miette::Result<()> {
    // If the input is a .eclb file, load and execute via VM
    if eclexia_codegen::bytecode::BytecodeModule::is_eclb_path(input) {
        return run_bytecode(input, observe_shadow, carbon_report);
    }

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
        return Err(miette::miette!(
            "Parsing failed with {} errors",
            parse_errors.len()
        ));
    }

    // Module resolution + interface generation
    compile_module_graph(input)?;

    if observe_shadow {
        let registry = eclexia_runtime::ShadowPriceRegistry::new();
        let energy = registry.get_price(
            &smol_str::SmolStr::new("energy"),
            eclexia_ast::dimension::Dimension::energy(),
        );
        let time = registry.get_price(
            &smol_str::SmolStr::new("time"),
            eclexia_ast::dimension::Dimension::time(),
        );
        let carbon = registry.get_price(
            &smol_str::SmolStr::new("carbon"),
            eclexia_ast::dimension::Dimension::carbon(),
        );
        println!(
            "Shadow price observation: λ_energy={:.6}, λ_time={:.6}, λ_carbon={:.6}",
            energy, time, carbon
        );
    }

    // Execute using the interpreter
    println!("Running {}...\n", input.display());

    match eclexia_interp::run(&file) {
        Ok(result) => {
            println!("\nResult: {:?}", result);

            if carbon_report {
                // NOTE: Interpreter resource usage not yet wired into this report.
                println!("\n--- Carbon Report ---");
                println!("  Energy used:  (tracked)");
                println!("  Carbon used:  (tracked)");
            }

            Ok(())
        }
        Err(e) => Err(miette::miette!("Runtime error: {}", e)),
    }
}

/// Run a pre-compiled .eclb bytecode file through the VM.
fn run_bytecode(input: &Path, observe_shadow: bool, carbon_report: bool) -> miette::Result<()> {
    use eclexia_codegen::bytecode::BytecodeModule;

    println!("Loading bytecode from {}...", input.display());

    let module = BytecodeModule::read_eclb(input).map_err(|e| miette::miette!("{}", e))?;

    println!(
        "  {} function(s), {} string(s)",
        module.functions.len(),
        module.strings.len()
    );

    let mut runtime = Runtime::new();

    // Execute through the VM
    let mut vm = eclexia_codegen::VirtualMachine::new(module);
    match vm.run() {
        Ok(result) => {
            println!("\nResult: {:?}", result);

            // Feed resource totals into the runtime tracker
            runtime.ingest_usage(
                vm.get_resources()
                    .iter()
                    .map(|entry| (entry.resource.clone(), entry.dimension, entry.amount)),
            );

            if carbon_report {
                let totals = vm.get_resource_usage();
                println!("\n--- Carbon Report ---");
                if totals.is_empty() {
                    println!("  No resource usage tracked");
                } else {
                    for (name, amount) in &totals {
                        println!("  {}: {:.4}", name, amount);
                    }
                }
            }

            if observe_shadow {
                let computed_prices = runtime.refresh_shadow_prices_from_usage();
                if computed_prices.is_empty() {
                    use eclexia_ast::dimension::Dimension;
                    let energy = runtime
                        .get_shadow_price(&smol_str::SmolStr::new("energy"), Dimension::energy());
                    let time = runtime
                        .get_shadow_price(&smol_str::SmolStr::new("time"), Dimension::time());
                    let carbon = runtime
                        .get_shadow_price(&smol_str::SmolStr::new("carbon"), Dimension::carbon());
                    println!(
                        "Shadow price observation: λ_energy={:.6}, λ_time={:.6}, λ_carbon={:.6}",
                        energy, time, carbon
                    );
                } else {
                    println!("\n--- Dynamic Shadow Prices (from runtime metrics) ---");
                    for (name, dimension, price) in &computed_prices {
                        println!("  {} ({:?}) = {:.6}", name, dimension, price);
                    }
                }
            }

            if let Some(sample) = runtime.capture_system_metrics() {
                println!("\n--- System Power Sample ---");
                println!("  Energy: {:.4} J", sample.energy_joules);
                println!("  Duration: {:.4} s", sample.duration_secs);
                println!("  Carbon: {:.4} gCO2e", sample.carbon_gco2e);
            } else if !PowerMetrics::is_available() {
                println!("\n--- System Power Sample ---");
                println!("  RAPL energy counter not available on this host");
            }

            Ok(())
        }
        Err(e) => Err(miette::miette!("VM error: {}", e)),
    }
}

/// Type check a file.
pub fn check(input: &Path) -> miette::Result<()> {
    let source = std::fs::read_to_string(input)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", input.display()))?;

    let (_file, parse_errors) = eclexia_parser::parse(&source);

    if !parse_errors.is_empty() {
        eprintln!("Parse errors:");
        for err in &parse_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!("Parsing failed"));
    }

    // Module resolution + interface generation
    compile_module_graph(input)?;

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
        } else if !check {
            println!("✓ {} (no changes needed)", input.display());
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

/// Serve the runtime health endpoints for Kubernetes probes.
pub fn serve_health(bind: &str) -> miette::Result<()> {
    let runtime = Arc::new(Mutex::new(Runtime::new()));
    let server = HealthServer::new(bind, runtime);
    server
        .run()
        .map_err(|err| miette::miette!("health server failed: {}", err))
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
        return Err(miette::miette!(
            "Project name cannot contain '..' (path traversal)"
        ));
    }

    // Reject path separators (require simple names)
    if name.contains('/') || name.contains('\\') {
        return Err(miette::miette!(
            "Project name cannot contain path separators"
        ));
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
    let config = format!(
        r#"# SPDX-License-Identifier: MIT
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
"#,
        project_name
    );

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

/// Create a new project from a template.
///
/// Supported templates:
/// - `bin` — Binary application (default)
/// - `lib` — Reusable library
/// - `web` — TEA web application framework
/// - `cli` — Command-line tool
/// - `mcp` — MCP server for AI agents
/// - `ssg` — Static site generator engine
/// - `lsp` — Language server protocol extension
/// - `tool` — Developer tool/utility
/// - `framework` — Application framework
/// - `db-connector` — Database connector (Idris2 ABI + Zig FFI + eclexia binding)
pub fn new_project(name: &str, template: &str) -> miette::Result<()> {
    let name = sanitize_project_name(name)?;

    let templates = [
        "bin",
        "lib",
        "web",
        "cli",
        "mcp",
        "ssg",
        "lsp",
        "tool",
        "framework",
        "db-connector",
    ];

    if !templates.contains(&template) {
        return Err(miette::miette!(
            "Unknown template '{}'. Available templates:\n  {}",
            template,
            templates.join(", ")
        ));
    }

    println!("Creating new Eclexia {} project: {}", template, name);

    // Create base directory structure
    std::fs::create_dir_all(format!("{}/src", name)).into_diagnostic()?;

    // Generate template-specific files
    match template {
        "bin" => mint_bin(name)?,
        "lib" => mint_lib(name)?,
        "web" => mint_web(name)?,
        "cli" => mint_cli(name)?,
        "mcp" => mint_mcp(name)?,
        "ssg" => mint_ssg(name)?,
        "lsp" => mint_lsp(name)?,
        "tool" => mint_tool(name)?,
        "framework" => mint_framework(name)?,
        "db-connector" => mint_db_connector(name)?,
        _ => unreachable!(),
    }

    // Create common files for all templates
    mint_common_files(name, template)?;

    println!("\n✓ Created {} project in {}/", template, name);
    println!();
    println!("To get started:");
    println!("  cd {}", name);
    match template {
        "lib" => println!("  eclexia check src/lib.ecl"),
        "web" => {
            println!("  eclexia run src/main.ecl");
            println!("  # Then open http://localhost:8080");
        }
        "mcp" => {
            println!("  eclexia run src/main.ecl");
            println!("  # MCP server listens on stdin/stdout");
        }
        "db-connector" => {
            println!("  # 1. Review src/abi/Types.idr (Idris2 ABI spec)");
            println!("  # 2. Build ffi/zig: cd ffi/zig && zig build");
            println!("  # 3. Use binding: eclexia run src/main.ecl");
        }
        _ => println!("  eclexia run src/main.ecl"),
    }

    Ok(())
}

/// Generate common files for all project templates.
fn mint_common_files(name: &str, template: &str) -> miette::Result<()> {
    // .gitignore
    let gitignore = "# Eclexia build artifacts\n\
        /target/\n\
        *.eclo\n\
        *.eclprof\n\
        \n\
        # IDE\n\
        .vscode/\n\
        .idea/\n\
        \n\
        # OS\n\
        .DS_Store\n\
        Thumbs.db\n";
    std::fs::write(format!("{}/.gitignore", name), gitignore).into_diagnostic()?;

    // README
    let readme = format!(
        "# {}\n\n\
        An Eclexia {} project.\n\n\
        ## Getting Started\n\n\
        ```bash\n\
        eclexia run src/main.ecl\n\
        ```\n\n\
        ## License\n\n\
        PMPL-1.0-or-later\n",
        name, template
    );
    std::fs::write(format!("{}/README.md", name), readme).into_diagnostic()?;

    // eclexia.toml (template-aware)
    let output_type = match template {
        "lib" | "framework" => "lib",
        _ => "bin",
    };
    let config = format!(
        "# SPDX-License-Identifier: PMPL-1.0-or-later\n\
        # Eclexia project configuration\n\n\
        [package]\n\
        name = \"{name}\"\n\
        version = \"0.1.0\"\n\
        edition = \"2025\"\n\
        license = \"PMPL-1.0-or-later\"\n\
        description = \"An Eclexia {template} project\"\n\
        authors = [\"Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>\"]\n\n\
        [build]\n\
        output-type = \"{output_type}\"\n\n\
        [dependencies]\n\
        # Add your dependencies here\n\n\
        [resources]\n\
        default-energy-budget = \"1000J\"\n\
        default-carbon-budget = \"100gCO2e\"\n",
        name = name,
        template = template,
        output_type = output_type
    );
    std::fs::write(format!("{}/eclexia.toml", name), config).into_diagnostic()?;

    // tests directory
    std::fs::create_dir_all(format!("{}/tests", name)).into_diagnostic()?;

    Ok(())
}

/// Mint a binary application project.
fn mint_bin(name: &str) -> miette::Result<()> {
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An Eclexia application.\n\n\
        def main() -> Unit\n\
        \x20   @requires: energy < 10J\n\
        {{\n\
        \x20   println(\"Hello from {name}!\")\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;

    let test = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! Tests for {name}.\n\n\
        #[test]\n\
        def test_hello() -> Unit {{\n\
        \x20   assert(true, \"basic assertion\")\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/tests/main_test.ecl", name), test).into_diagnostic()?;
    Ok(())
}

/// Mint a library project.
fn mint_lib(name: &str) -> miette::Result<()> {
    let lib = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An Eclexia library.\n\
        //!\n\
        //! ## Usage\n\
        //!\n\
        //! ```eclexia\n\
        //! import {name}\n\
        //!\n\
        //! def main() -> Unit {{\n\
        //!     let result = {name}::greet(\"World\")\n\
        //!     println(result)\n\
        //! }}\n\
        //! ```\n\n\
        /// Greet someone by name.\n\
        pub def greet(who: String) -> String\n\
        \x20   @requires: energy < 1J\n\
        {{\n\
        \x20   string_concat(\"Hello, \", string_concat(who, \"!\"))\n\
        }}\n\n\
        /// Get the library version.\n\
        pub def version() -> String {{\n\
        \x20   \"0.1.0\"\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/lib.ecl", name), lib).into_diagnostic()?;

    let test = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! Tests for {name}.\n\n\
        import {name}\n\n\
        #[test]\n\
        def test_greet() -> Unit {{\n\
        \x20   let result = {name}::greet(\"World\")\n\
        \x20   assert_eq(result, \"Hello, World!\", \"greeting should match\")\n\
        }}\n\n\
        #[test]\n\
        def test_version() -> Unit {{\n\
        \x20   let v = {name}::version()\n\
        \x20   assert(string_len(v) > 0, \"version should not be empty\")\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/tests/lib_test.ecl", name), test).into_diagnostic()?;
    Ok(())
}

/// Mint a TEA web application project.
fn mint_web(name: &str) -> miette::Result<()> {
    std::fs::create_dir_all(format!("{}/src/components", name)).into_diagnostic()?;

    // Main entry point with TEA architecture
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — A TEA (The Elm Architecture) web application.\n\
        //!\n\
        //! Model-Update-View architecture with resource-aware rendering.\n\n\
        import tea\n\
        import tea/html\n\
        import tea/cmd\n\n\
        //==========================================================================\n\
        // Model\n\
        //==========================================================================\n\n\
        /// Application state.\n\
        type Model {{\n\
        \x20   count: Int,\n\
        \x20   message: String,\n\
        }}\n\n\
        /// Initialize the model.\n\
        def init() -> (Model, Cmd<Msg>)\n\
        \x20   @requires: energy < 1J\n\
        {{\n\
        \x20   let model = Model {{ count: 0, message: \"Welcome to {name}!\" }}\n\
        \x20   (model, cmd::none())\n\
        }}\n\n\
        //==========================================================================\n\
        // Messages\n\
        //==========================================================================\n\n\
        /// Messages that can update the model.\n\
        type Msg {{\n\
        \x20   Increment,\n\
        \x20   Decrement,\n\
        \x20   Reset,\n\
        \x20   SetMessage(String),\n\
        }}\n\n\
        //==========================================================================\n\
        // Update\n\
        //==========================================================================\n\n\
        /// Update the model in response to a message.\n\
        def update(model: Model, msg: Msg) -> (Model, Cmd<Msg>)\n\
        \x20   @requires: energy < 5J\n\
        {{\n\
        \x20   match msg {{\n\
        \x20       Increment => (Model {{ ..model, count: model.count + 1 }}, cmd::none()),\n\
        \x20       Decrement => (Model {{ ..model, count: model.count - 1 }}, cmd::none()),\n\
        \x20       Reset => (Model {{ ..model, count: 0 }}, cmd::none()),\n\
        \x20       SetMessage(text) => (Model {{ ..model, message: text }}, cmd::none()),\n\
        \x20   }}\n\
        }}\n\n\
        //==========================================================================\n\
        // View\n\
        //==========================================================================\n\n\
        /// Render the model as HTML.\n\
        def view(model: Model) -> Html<Msg>\n\
        \x20   @requires: energy < 10J\n\
        {{\n\
        \x20   html::div([], [\n\
        \x20       html::h1([], [html::text(model.message)]),\n\
        \x20       html::p([], [html::text(int_to_string(model.count))]),\n\
        \x20       html::button([html::on_click(Increment)], [html::text(\"+\")]),\n\
        \x20       html::button([html::on_click(Decrement)], [html::text(\"-\")]),\n\
        \x20       html::button([html::on_click(Reset)], [html::text(\"Reset\")]),\n\
        \x20   ])\n\
        }}\n\n\
        //==========================================================================\n\
        // Main\n\
        //==========================================================================\n\n\
        /// Mount the TEA application.\n\
        def main() -> Unit {{\n\
        \x20   tea::mount(\"#app\", init, update, view)\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;

    // Router component (compatible with cadre-router pattern)
    let router = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! Router for {name} — type-safe URL routing.\n\
        //!\n\
        //! Compatible with cadre-router patterns.\n\n\
        import tea/router\n\n\
        /// Route variants for the application.\n\
        type Route {{\n\
        \x20   Home,\n\
        \x20   About,\n\
        \x20   NotFound,\n\
        }}\n\n\
        /// Parse a URL path into a typed route.\n\
        pub def parse_route(path: String) -> Route {{\n\
        \x20   match path {{\n\
        \x20       \"/\" => Home,\n\
        \x20       \"/about\" => About,\n\
        \x20       _ => NotFound,\n\
        \x20   }}\n\
        }}\n\n\
        /// Serialize a route to a URL path.\n\
        pub def route_to_string(route: Route) -> String {{\n\
        \x20   match route {{\n\
        \x20       Home => \"/\",\n\
        \x20       About => \"/about\",\n\
        \x20       NotFound => \"/404\",\n\
        \x20   }}\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/components/router.ecl", name), router).into_diagnostic()?;

    // index.html
    let html = format!(
        "<!DOCTYPE html>\n\
        <html lang=\"en\">\n\
        <head>\n\
        \x20   <meta charset=\"UTF-8\">\n\
        \x20   <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n\
        \x20   <title>{name}</title>\n\
        </head>\n\
        <body>\n\
        \x20   <div id=\"app\"></div>\n\
        \x20   <script type=\"module\" src=\"/target/main.js\"></script>\n\
        </body>\n\
        </html>\n",
        name = name
    );
    std::fs::write(format!("{}/index.html", name), html).into_diagnostic()?;

    Ok(())
}

/// Mint a CLI tool project.
fn mint_cli(name: &str) -> miette::Result<()> {
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — A command-line tool.\n\n\
        /// CLI argument configuration.\n\
        type Args {{\n\
        \x20   command: String,\n\
        \x20   verbose: Bool,\n\
        \x20   input: Option<String>,\n\
        }}\n\n\
        /// Parse command-line arguments.\n\
        def parse_args(argv: Array<String>) -> Args {{\n\
        \x20   Args {{\n\
        \x20       command: if array_len(argv) > 1 {{ array_get(argv, 1).unwrap_or(\"help\") }} else {{ \"help\" }},\n\
        \x20       verbose: false,\n\
        \x20       input: if array_len(argv) > 2 {{ array_get(argv, 2) }} else {{ None }},\n\
        \x20   }}\n\
        }}\n\n\
        /// Run a command.\n\
        def run_command(args: Args) -> Result<Unit, String>\n\
        \x20   @requires: energy < 100J\n\
        {{\n\
        \x20   match args.command {{\n\
        \x20       \"help\" => {{\n\
        \x20           println(\"Usage: {name} <command> [options]\")\n\
        \x20           println(\"\")\n\
        \x20           println(\"Commands:\")\n\
        \x20           println(\"  help    Show this help\")\n\
        \x20           println(\"  version Show version\")\n\
        \x20           Ok(())\n\
        \x20       }},\n\
        \x20       \"version\" => {{\n\
        \x20           println(\"{name} 0.1.0\")\n\
        \x20           Ok(())\n\
        \x20       }},\n\
        \x20       _ => Err(string_concat(\"Unknown command: \", args.command)),\n\
        \x20   }}\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let args = parse_args(@builtin(\"argv\"))\n\
        \x20   match run_command(args) {{\n\
        \x20       Ok(_) => (),\n\
        \x20       Err(e) => {{\n\
        \x20           println(string_concat(\"Error: \", e))\n\
        \x20       }},\n\
        \x20   }}\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;
    Ok(())
}

/// Mint an MCP server project.
fn mint_mcp(name: &str) -> miette::Result<()> {
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An MCP (Model Context Protocol) server.\n\
        //!\n\
        //! Exposes tools for AI agents over stdin/stdout JSON-RPC.\n\n\
        import mcp\n\
        import json\n\n\
        /// Define the tools this MCP server provides.\n\
        def register_tools(server: mcp::Server) -> mcp::Server {{\n\
        \x20   server\n\
        \x20       .add_tool(mcp::Tool {{\n\
        \x20           name: \"hello\",\n\
        \x20           description: \"Greet someone\",\n\
        \x20           input_schema: json::object([\n\
        \x20               (\"name\", json::string_schema(\"Name to greet\")),\n\
        \x20           ]),\n\
        \x20           handler: handle_hello,\n\
        \x20       }})\n\
        \x20       .add_tool(mcp::Tool {{\n\
        \x20           name: \"analyze\",\n\
        \x20           description: \"Analyze resource usage of an expression\",\n\
        \x20           input_schema: json::object([\n\
        \x20               (\"expression\", json::string_schema(\"Eclexia expression to analyze\")),\n\
        \x20           ]),\n\
        \x20           handler: handle_analyze,\n\
        \x20       }})\n\
        }}\n\n\
        /// Handle the 'hello' tool.\n\
        def handle_hello(params: json::Value) -> Result<json::Value, String>\n\
        \x20   @requires: energy < 1J\n\
        {{\n\
        \x20   let name = json::get_string(params, \"name\").unwrap_or(\"World\")\n\
        \x20   Ok(json::string(string_concat(\"Hello, \", string_concat(name, \"!\"))))\n\
        }}\n\n\
        /// Handle the 'analyze' tool.\n\
        def handle_analyze(params: json::Value) -> Result<json::Value, String>\n\
        \x20   @requires: energy < 50J\n\
        {{\n\
        \x20   let expr = json::get_string(params, \"expression\")\n\
        \x20   match expr {{\n\
        \x20       Some(e) => Ok(json::object([\n\
        \x20           (\"expression\", json::string(e)),\n\
        \x20           (\"estimated_energy\", json::string(\"<1J\")),\n\
        \x20           (\"status\", json::string(\"within budget\")),\n\
        \x20       ])),\n\
        \x20       None => Err(\"Missing 'expression' parameter\"),\n\
        \x20   }}\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let server = mcp::Server::new(\"{name}\", \"0.1.0\")\n\
        \x20   let server = register_tools(server)\n\
        \x20   mcp::serve_stdio(server)\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;
    Ok(())
}

/// Mint an SSG engine project.
fn mint_ssg(name: &str) -> miette::Result<()> {
    std::fs::create_dir_all(format!("{}/src/templates", name)).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/content", name)).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/output", name)).into_diagnostic()?;

    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — A resource-aware static site generator.\n\
        //!\n\
        //! Generates static HTML from content files with energy/carbon budgets.\n\n\
        import io\n\
        import text\n\n\
        /// Site configuration.\n\
        type SiteConfig {{\n\
        \x20   title: String,\n\
        \x20   base_url: String,\n\
        \x20   content_dir: String,\n\
        \x20   output_dir: String,\n\
        }}\n\n\
        /// A content page.\n\
        type Page {{\n\
        \x20   title: String,\n\
        \x20   slug: String,\n\
        \x20   body: String,\n\
        }}\n\n\
        /// Build the entire site.\n\
        def build_site(config: SiteConfig) -> Result<Int, String>\n\
        \x20   @requires: energy < 100J\n\
        \x20   @requires: carbon < 10gCO2e\n\
        {{\n\
        \x20   let pages = scan_content(config.content_dir)\n\
        \x20   let count = array_len(pages)\n\
        \x20   // Render each page\n\
        \x20   println(string_concat(\"Building \", string_concat(int_to_string(count), \" pages...\")))\n\
        \x20   Ok(count)\n\
        }}\n\n\
        /// Scan content directory for pages.\n\
        def scan_content(dir: String) -> Array<Page> {{\n\
        \x20   // Placeholder: read .ecl content files from directory\n\
        \x20   [Page {{ title: \"Home\", slug: \"index\", body: \"Welcome!\" }}]\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let config = SiteConfig {{\n\
        \x20       title: \"{name}\",\n\
        \x20       base_url: \"https://example.com\",\n\
        \x20       content_dir: \"content\",\n\
        \x20       output_dir: \"output\",\n\
        \x20   }}\n\
        \x20   match build_site(config) {{\n\
        \x20       Ok(n) => println(string_concat(\"Built \", string_concat(int_to_string(n), \" pages\"))),\n\
        \x20       Err(e) => println(string_concat(\"Error: \", e)),\n\
        \x20   }}\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;
    Ok(())
}

/// Mint an LSP extension project.
fn mint_lsp(name: &str) -> miette::Result<()> {
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An Eclexia language server extension.\n\
        //!\n\
        //! Extends the base eclexia-lsp with custom diagnostics or completions.\n\n\
        import lsp\n\n\
        /// Custom diagnostic provider.\n\
        pub def custom_diagnostics(source: String) -> Array<lsp::Diagnostic> {{\n\
        \x20   // Add custom lint rules or domain-specific checks\n\
        \x20   []\n\
        }}\n\n\
        /// Custom completion provider.\n\
        pub def custom_completions(prefix: String, context: lsp::Context) -> Array<lsp::CompletionItem> {{\n\
        \x20   // Add domain-specific completions\n\
        \x20   []\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let server = lsp::Server::new(\"{name}\", \"0.1.0\")\n\
        \x20   let server = server\n\
        \x20       .add_diagnostics_provider(custom_diagnostics)\n\
        \x20       .add_completion_provider(custom_completions)\n\
        \x20   lsp::serve_stdio(server)\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;
    Ok(())
}

/// Mint a developer tool project.
fn mint_tool(name: &str) -> miette::Result<()> {
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An Eclexia developer tool.\n\n\
        /// Tool configuration.\n\
        type Config {{\n\
        \x20   verbose: Bool,\n\
        \x20   dry_run: Bool,\n\
        }}\n\n\
        /// Run the tool with the given configuration.\n\
        pub def run(config: Config, inputs: Array<String>) -> Result<Unit, String>\n\
        \x20   @requires: energy < 50J\n\
        {{\n\
        \x20   if config.verbose {{\n\
        \x20       println(string_concat(\"Processing \", int_to_string(array_len(inputs))))\n\
        \x20   }}\n\
        \x20   // Tool logic here\n\
        \x20   Ok(())\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let config = Config {{ verbose: true, dry_run: false }}\n\
        \x20   match run(config, []) {{\n\
        \x20       Ok(_) => println(\"Done.\"),\n\
        \x20       Err(e) => println(string_concat(\"Error: \", e)),\n\
        \x20   }}\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;
    Ok(())
}

/// Mint an application framework project.
fn mint_framework(name: &str) -> miette::Result<()> {
    std::fs::create_dir_all(format!("{}/src/middleware", name)).into_diagnostic()?;

    let lib = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — An Eclexia application framework.\n\
        //!\n\
        //! Provides middleware, routing, and lifecycle management\n\
        //! with resource-aware execution.\n\n\
        /// Application context passed through middleware.\n\
        pub type Context {{\n\
        \x20   request: Request,\n\
        \x20   response: Response,\n\
        \x20   state: Map<String, String>,\n\
        }}\n\n\
        /// HTTP request.\n\
        pub type Request {{\n\
        \x20   method: String,\n\
        \x20   path: String,\n\
        \x20   headers: Map<String, String>,\n\
        \x20   body: Option<String>,\n\
        }}\n\n\
        /// HTTP response.\n\
        pub type Response {{\n\
        \x20   status: Int,\n\
        \x20   headers: Map<String, String>,\n\
        \x20   body: String,\n\
        }}\n\n\
        /// Middleware function type.\n\
        pub type Middleware = fn(Context, fn(Context) -> Context) -> Context\n\n\
        /// Application builder.\n\
        pub type App {{\n\
        \x20   middlewares: Array<Middleware>,\n\
        \x20   routes: Array<Route>,\n\
        }}\n\n\
        /// Route definition.\n\
        pub type Route {{\n\
        \x20   method: String,\n\
        \x20   path: String,\n\
        \x20   handler: fn(Context) -> Context,\n\
        }}\n\n\
        /// Create a new application.\n\
        pub def new() -> App {{\n\
        \x20   App {{ middlewares: [], routes: [] }}\n\
        }}\n\n\
        /// Add middleware to the application.\n\
        pub def use_middleware(app: App, mw: Middleware) -> App {{\n\
        \x20   App {{ ..app, middlewares: array_push(app.middlewares, mw) }}\n\
        }}\n\n\
        /// Add a route to the application.\n\
        pub def route(app: App, method: String, path: String, handler: fn(Context) -> Context) -> App {{\n\
        \x20   let r = Route {{ method: method, path: path, handler: handler }}\n\
        \x20   App {{ ..app, routes: array_push(app.routes, r) }}\n\
        }}\n\n\
        /// Start the application.\n\
        pub def listen(app: App, port: Int) -> Result<Unit, String>\n\
        \x20   @requires: energy < 1000J\n\
        {{\n\
        \x20   println(string_concat(\"Listening on port \", int_to_string(port)))\n\
        \x20   Ok(())\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/lib.ecl", name), lib).into_diagnostic()?;

    let example = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! Example application using {name}.\n\n\
        import {name}\n\n\
        def handle_index(ctx: {name}::Context) -> {name}::Context {{\n\
        \x20   {{ ..ctx, response: {{ ..ctx.response, status: 200, body: \"Hello!\" }} }}\n\
        }}\n\n\
        def main() -> Unit {{\n\
        \x20   let app = {name}::new()\n\
        \x20       .route(\"GET\", \"/\", handle_index)\n\
        \x20   {name}::listen(app, 8080)\n\
        }}\n",
        name = name
    );
    std::fs::write(format!("{}/src/main.ecl", name), example).into_diagnostic()?;
    Ok(())
}

/// Mint a database connector project (Idris2 ABI + Zig FFI + Eclexia binding).
fn mint_db_connector(name: &str) -> miette::Result<()> {
    // Create the three-layer directory structure
    std::fs::create_dir_all(format!("{}/src/abi", name)).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/ffi/zig/src", name)).into_diagnostic()?;
    std::fs::create_dir_all(format!("{}/ffi/zig/test", name)).into_diagnostic()?;

    // Idris2 ABI spec
    let abi = format!(
        "-- SPDX-License-Identifier: PMPL-1.0-or-later\n\
        -- {name} database connector ABI definitions\n\
        --\n\
        -- Formally verified interface with dependent type proofs.\n\n\
        module {capitalized}.ABI.Types\n\n\
        ||| Connection handle (opaque, non-null after successful connect).\n\
        export\n\
        data ConnHandle : Type where\n\
        \x20 MkConnHandle : Ptr -> ConnHandle\n\n\
        ||| Result of a database operation.\n\
        public export\n\
        data DBResult : Type -> Type where\n\
        \x20 DBOk    : a -> DBResult a\n\
        \x20 DBError : String -> DBResult a\n\n\
        ||| Query result row.\n\
        public export\n\
        record Row where\n\
        \x20 constructor MkRow\n\
        \x20 columns : List (String, String)\n\n\
        ||| Connection configuration.\n\
        public export\n\
        record ConnConfig where\n\
        \x20 constructor MkConnConfig\n\
        \x20 host     : String\n\
        \x20 port     : Nat\n\
        \x20 database : String\n\
        \x20 user     : String\n\
        \x20 password : String\n\n\
        ||| Proof that port is in valid range.\n\
        export\n\
        validPort : (n : Nat) -> Dec (LTE 1 n, LTE n 65535)\n",
        name = name,
        capitalized = capitalize(name)
    );
    std::fs::write(format!("{}/src/abi/Types.idr", name), abi).into_diagnostic()?;

    // Zig FFI implementation
    let ffi = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        // {name} database connector FFI implementation\n\n\
        const std = @import(\"std\");\n\n\
        pub const ConnHandle = opaque {{}};\n\n\
        pub const Result = enum(c_int) {{\n\
        \x20   ok = 0,\n\
        \x20   connection_failed = 1,\n\
        \x20   query_failed = 2,\n\
        \x20   invalid_param = 3,\n\
        \x20   null_pointer = 4,\n\
        }};\n\n\
        export fn {name_under}_connect(\n\
        \x20   host: [*:0]const u8,\n\
        \x20   port: u16,\n\
        \x20   database: [*:0]const u8,\n\
        \x20   user: [*:0]const u8,\n\
        \x20   password: [*:0]const u8,\n\
        ) ?*ConnHandle {{\n\
        \x20   // NOTE: Link against database client library\n\
        \x20   _ = .{{ host, port, database, user, password }};\n\
        \x20   return null;\n\
        }}\n\n\
        export fn {name_under}_disconnect(handle: ?*ConnHandle) void {{\n\
        \x20   _ = handle;\n\
        }}\n\n\
        export fn {name_under}_query(\n\
        \x20   handle: ?*ConnHandle,\n\
        \x20   sql: [*:0]const u8,\n\
        ) Result {{\n\
        \x20   _ = .{{ handle, sql }};\n\
        \x20   return .ok;\n\
        }}\n",
        name = name,
        name_under = name.replace('-', "_")
    );
    std::fs::write(format!("{}/ffi/zig/src/main.zig", name), ffi).into_diagnostic()?;

    // Zig build file
    let build_zig = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\n\
        const std = @import(\"std\");\n\n\
        pub fn build(b: *std.Build) void {{\n\
        \x20   const target = b.standardTargetOptions(.{{}});\n\
        \x20   const optimize = b.standardOptimizeOption(.{{}});\n\n\
        \x20   const lib = b.addSharedLibrary(.{{\n\
        \x20       .name = \"{name_under}\",\n\
        \x20       .root_source_file = b.path(\"src/main.zig\"),\n\
        \x20       .target = target,\n\
        \x20       .optimize = optimize,\n\
        \x20   }});\n\
        \x20   b.installArtifact(lib);\n\n\
        \x20   const tests = b.addTest(.{{\n\
        \x20       .root_source_file = b.path(\"src/main.zig\"),\n\
        \x20       .target = target,\n\
        \x20       .optimize = optimize,\n\
        \x20   }});\n\
        \x20   const test_step = b.step(\"test\", \"Run tests\");\n\
        \x20   test_step.dependOn(&b.addRunArtifact(tests).step);\n\
        }}\n",
        name_under = name.replace('-', "_")
    );
    std::fs::write(format!("{}/ffi/zig/build.zig", name), build_zig).into_diagnostic()?;

    // Eclexia binding (user-facing API)
    let binding = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! {name} — Database connector for Eclexia.\n\
        //!\n\
        //! ## Usage\n\
        //!\n\
        //! ```eclexia\n\
        //! import {name_under}\n\
        //!\n\
        //! def main() -> Unit {{\n\
        //!     let conn = {name_under}::connect(\"localhost\", 5432, \"mydb\", \"user\", \"pass\")\n\
        //!     let rows = conn.query(\"SELECT * FROM users\")\n\
        //! }}\n\
        //! ```\n\n\
        /// Database connection.\n\
        pub type Connection {{\n\
        \x20   handle: @extern_ptr,\n\
        }}\n\n\
        /// Query result.\n\
        pub type QueryResult {{\n\
        \x20   rows: Array<Row>,\n\
        \x20   affected: Int,\n\
        }}\n\n\
        /// A result row.\n\
        pub type Row {{\n\
        \x20   columns: Array<(String, String)>,\n\
        }}\n\n\
        // FFI declarations\n\
        extern \"C\" {{\n\
        \x20   fn {name_under}_connect(host: Ptr, port: Int, db: Ptr, user: Ptr, pass: Ptr) -> Ptr;\n\
        \x20   fn {name_under}_disconnect(handle: Ptr) -> Unit;\n\
        \x20   fn {name_under}_query(handle: Ptr, sql: Ptr) -> Int;\n\
        }}\n\n\
        /// Connect to the database.\n\
        pub def connect(host: String, port: Int, database: String, user: String, password: String) -> Result<Connection, String>\n\
        \x20   @requires: energy < 50J\n\
        {{\n\
        \x20   let handle = {name_under}_connect(host, port, database, user, password)\n\
        \x20   if handle == null {{\n\
        \x20       Err(\"Connection failed\")\n\
        \x20   }} else {{\n\
        \x20       Ok(Connection {{ handle: handle }})\n\
        \x20   }}\n\
        }}\n\n\
        /// Execute a query.\n\
        pub def query(conn: Connection, sql: String) -> Result<QueryResult, String>\n\
        \x20   @requires: energy < 100J\n\
        {{\n\
        \x20   let result = {name_under}_query(conn.handle, sql)\n\
        \x20   if result == 0 {{\n\
        \x20       Ok(QueryResult {{ rows: [], affected: 0 }})\n\
        \x20   }} else {{\n\
        \x20       Err(\"Query failed\")\n\
        \x20   }}\n\
        }}\n\n\
        /// Close the connection.\n\
        pub def disconnect(conn: Connection) -> Unit {{\n\
        \x20   {name_under}_disconnect(conn.handle)\n\
        }}\n",
        name = name, name_under = name.replace('-', "_")
    );
    std::fs::write(format!("{}/src/lib.ecl", name), binding).into_diagnostic()?;

    // Example main using the connector
    let main = format!(
        "// SPDX-License-Identifier: PMPL-1.0-or-later\n\
        //! Example usage of {name} connector.\n\n\
        import {name_under}\n\n\
        def main() -> Unit {{\n\
        \x20   match {name_under}::connect(\"localhost\", 5432, \"testdb\", \"user\", \"pass\") {{\n\
        \x20       Ok(conn) => {{\n\
        \x20           println(\"Connected!\")\n\
        \x20           match {name_under}::query(conn, \"SELECT 1\") {{\n\
        \x20               Ok(result) => println(\"Query ok\"),\n\
        \x20               Err(e) => println(string_concat(\"Query error: \", e)),\n\
        \x20           }}\n\
        \x20           {name_under}::disconnect(conn)\n\
        \x20       }},\n\
        \x20       Err(e) => println(string_concat(\"Connection error: \", e)),\n\
        \x20   }}\n\
        }}\n",
        name = name, name_under = name.replace('-', "_")
    );
    std::fs::write(format!("{}/src/main.ecl", name), main).into_diagnostic()?;

    Ok(())
}

/// Capitalize the first letter of a string.
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Run tests.
pub fn test(filter: Option<&str>) -> miette::Result<()> {
    use crate::test_runner;

    // Look for test files in src/ and tests/
    let test_patterns = ["src/**/*.ecl", "tests/**/*.ecl"];
    let mut test_files = Vec::new();

    for pattern in test_patterns {
        for path in glob::glob(pattern).into_diagnostic()?.flatten() {
            test_files.push(path);
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
pub fn bench(filter: Option<&str>, energy_enabled: bool) -> miette::Result<()> {
    use crate::bench_runner;

    // Look for benchmark files in src/ and benches/
    let bench_patterns = ["src/**/*.ecl", "benches/**/*.ecl"];
    let mut bench_files = Vec::new();

    for pattern in bench_patterns {
        for path in glob::glob(pattern).into_diagnostic()?.flatten() {
            bench_files.push(path);
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

        let summary =
            bench_runner::run_all_benchmarks(&file, filter, ITERATIONS, true, energy_enabled);
        total_summary.benchmarks_run += summary.benchmarks_run;
        total_summary.benchmarks_failed += summary.benchmarks_failed;
        total_summary.benchmarks_ignored += summary.benchmarks_ignored;
    }

    // Exit with error code if benchmarks failed
    if total_summary.benchmarks_failed > 0 {
        return Err(miette::miette!(
            "{} benchmarks failed",
            total_summary.benchmarks_failed
        ));
    }

    if total_summary.benchmarks_run == 0 {
        println!("No benchmarks found.");
        println!("Add #[bench] attribute to functions to mark them as benchmarks.");
        return Ok(());
    }

    println!("✓ All {} benchmarks passed", total_summary.benchmarks_run);
    Ok(())
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Default)]
struct MigrationState {
    applied: Vec<String>,
}

/// Profile a program and emit timing/resource reports.
pub fn profile(
    input: &Path,
    output: Option<&Path>,
    format: &str,
    observe_shadow: bool,
    carbon_report: bool,
) -> miette::Result<()> {
    use eclexia_ast::dimension::Dimension;
    use serde_json::json;
    use smol_str::SmolStr;

    if eclexia_codegen::bytecode::BytecodeModule::is_eclb_path(input)
        && format == "json"
        && output.is_none()
    {
        return Err(miette::miette!(
            "JSON profiling for bytecode requires --output to avoid mixed stdout from the program"
        ));
    }

    let total_start = Instant::now();
    let mut stages: Vec<(String, f64)> = Vec::new();

    let mut resources = serde_json::Map::new();
    let mut shadow = serde_json::Map::new();
    let result_repr: String;
    let program_output: String;
    let mode: &str;

    if eclexia_codegen::bytecode::BytecodeModule::is_eclb_path(input) {
        mode = "bytecode";

        let t0 = Instant::now();
        let module = eclexia_codegen::bytecode::BytecodeModule::read_eclb(input)
            .map_err(|e| miette::miette!("{}", e))?;
        stages.push((
            "load_bytecode".to_string(),
            t0.elapsed().as_secs_f64() * 1000.0,
        ));

        let t1 = Instant::now();
        let mut vm = eclexia_codegen::VirtualMachine::new(module);
        let vm_result = vm.run().map_err(|e| miette::miette!("VM error: {}", e))?;
        stages.push((
            "execute_vm".to_string(),
            t1.elapsed().as_secs_f64() * 1000.0,
        ));
        result_repr = format!("{:?}", vm_result);
        program_output = String::new();

        for (name, amount) in vm.get_resource_usage() {
            resources.insert(name.to_string(), json!(amount));
        }

        if observe_shadow {
            let mut runtime = Runtime::new();
            runtime.ingest_usage(
                vm.get_resources()
                    .iter()
                    .map(|entry| (entry.resource.clone(), entry.dimension, entry.amount)),
            );
            let computed_prices = runtime.refresh_shadow_prices_from_usage();
            if computed_prices.is_empty() {
                shadow.insert(
                    "energy".to_string(),
                    json!(runtime.get_shadow_price(&SmolStr::new("energy"), Dimension::energy())),
                );
                shadow.insert(
                    "time".to_string(),
                    json!(runtime.get_shadow_price(&SmolStr::new("time"), Dimension::time())),
                );
                shadow.insert(
                    "carbon".to_string(),
                    json!(runtime.get_shadow_price(&SmolStr::new("carbon"), Dimension::carbon())),
                );
            } else {
                for (name, dimension, price) in computed_prices {
                    shadow.insert(format!("{}::{:?}", name, dimension), json!(price));
                }
            }
        }
    } else {
        mode = "interpreter";

        let t0 = Instant::now();
        let source = std::fs::read_to_string(input)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", input.display()))?;
        stages.push((
            "read_source".to_string(),
            t0.elapsed().as_secs_f64() * 1000.0,
        ));

        let t1 = Instant::now();
        let (file, parse_errors) = eclexia_parser::parse(&source);
        if !parse_errors.is_empty() {
            return Err(miette::miette!(
                "Parsing failed with {} errors",
                parse_errors.len()
            ));
        }
        stages.push(("parse".to_string(), t1.elapsed().as_secs_f64() * 1000.0));

        let t2 = Instant::now();
        let type_errors = eclexia_typeck::check(&file);
        if !type_errors.is_empty() {
            return Err(miette::miette!(
                "Type checking failed with {} errors",
                type_errors.len()
            ));
        }
        stages.push(("typecheck".to_string(), t2.elapsed().as_secs_f64() * 1000.0));

        let t3 = Instant::now();
        let (interp_result, captured_output) = eclexia_interp::run_capturing_output(&file)
            .map_err(|e| miette::miette!("Runtime error: {}", e))?;
        stages.push((
            "execute_interp".to_string(),
            t3.elapsed().as_secs_f64() * 1000.0,
        ));
        result_repr = format!("{:?}", interp_result);
        program_output = captured_output;

        if observe_shadow {
            let registry = eclexia_runtime::ShadowPriceRegistry::new();
            shadow.insert(
                "energy".to_string(),
                json!(registry.get_price(&SmolStr::new("energy"), Dimension::energy())),
            );
            shadow.insert(
                "time".to_string(),
                json!(registry.get_price(&SmolStr::new("time"), Dimension::time())),
            );
            shadow.insert(
                "carbon".to_string(),
                json!(registry.get_price(&SmolStr::new("carbon"), Dimension::carbon())),
            );
        }
    }

    let total_ms = total_start.elapsed().as_secs_f64() * 1000.0;
    let report_json = json!({
        "tool": "eclexia-profile",
        "input": input.display().to_string(),
        "mode": mode,
        "total_ms": total_ms,
        "stages": stages.iter().map(|(name, ms)| json!({ "name": name, "ms": ms })).collect::<Vec<_>>(),
        "result": result_repr,
        "program_output": program_output,
        "resource_usage": resources,
        "shadow_prices": shadow,
        "carbon_report": if carbon_report { json!("enabled") } else { json!("disabled") },
    });

    let rendered = match format {
        "json" => serde_json::to_string_pretty(&report_json)
            .into_diagnostic()
            .wrap_err("Failed to serialize profile report")?,
        "flamegraph" => stages
            .iter()
            .map(|(name, ms)| {
                let micros = (*ms * 1000.0).max(1.0) as u64;
                format!("eclexia;{} {}", name, micros)
            })
            .collect::<Vec<_>>()
            .join("\n"),
        other => {
            return Err(miette::miette!(
                "Unsupported profile format '{}'. Use 'json' or 'flamegraph'.",
                other
            ));
        }
    };

    if let Some(path) = output {
        std::fs::write(path, rendered)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to write {}", path.display()))?;
        println!("✓ Profile report written to {}", path.display());
    } else {
        println!("{}", rendered);
    }

    Ok(())
}

/// Run coverage analysis via cargo-tarpaulin.
pub fn coverage(output: Option<&Path>, format: &str) -> miette::Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.arg("tarpaulin");

    if format != "text" {
        cmd.arg("--out").arg(format);
    }

    if let Some(path) = output {
        cmd.arg("--output-dir").arg(path);
    }

    println!("Running coverage: {:?}", cmd);
    let status = cmd
        .status()
        .into_diagnostic()
        .wrap_err("Failed to execute cargo-tarpaulin. Is it installed?")?;

    if !status.success() {
        return Err(miette::miette!(
            "Coverage command failed. Install tarpaulin with: cargo install cargo-tarpaulin"
        ));
    }

    println!("✓ Coverage run completed");
    Ok(())
}

/// Run fuzzing target via cargo-fuzz.
pub fn fuzz(target: &str, runs: Option<u64>) -> miette::Result<()> {
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .into_diagnostic()
        .wrap_err("Failed to resolve workspace root")?;
    let fuzz_dir = workspace_root.join("fuzz");
    let fuzz_manifest = fuzz_dir.join("Cargo.toml");

    if !fuzz_manifest.exists() {
        return Err(miette::miette!(
            "Fuzz workspace not found at {}",
            fuzz_manifest.display()
        ));
    }

    let mut cmd = Command::new("cargo");
    cmd.current_dir(&fuzz_dir)
        .arg("+nightly")
        .arg("fuzz")
        .arg("run")
        .arg(target);

    if let Some(runs) = runs {
        cmd.arg("--").arg(format!("-runs={}", runs));
    }

    println!(
        "Running fuzz target '{}' in {}...",
        target,
        fuzz_dir.display()
    );
    let status = cmd
        .status()
        .into_diagnostic()
        .wrap_err("Failed to execute cargo-fuzz. Is it installed and on PATH?")?;

    if !status.success() {
        return Err(miette::miette!(
            "Fuzz command failed. Ensure nightly is installed (`rustup toolchain install nightly`), cargo-fuzz is installed (`cargo install cargo-fuzz`), and the target exists under fuzz/fuzz_targets."
        ));
    }

    println!("✓ Fuzz run completed");
    Ok(())
}

/// Apply file-based SQL migrations.
pub fn migrate(dir: &Path, dry_run: bool, list: bool) -> miette::Result<()> {
    std::fs::create_dir_all(dir)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to create {}", dir.display()))?;

    let state_file = dir.join(".eclexia-migrate-state.json");
    let mut state: MigrationState = if state_file.exists() {
        let raw = std::fs::read_to_string(&state_file)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", state_file.display()))?;
        serde_json::from_str(&raw).unwrap_or_default()
    } else {
        MigrationState::default()
    };

    let mut migrations: Vec<std::path::PathBuf> = std::fs::read_dir(dir)
        .into_diagnostic()?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.extension().and_then(|e| e.to_str()) == Some("sql"))
        .collect();
    migrations.sort();

    if migrations.is_empty() {
        println!("No migrations found in {}", dir.display());
        return Ok(());
    }

    if list {
        println!("Migration status:");
        for migration in &migrations {
            let name = migration
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("<unknown>");
            let status = if state.applied.iter().any(|applied| applied == name) {
                "applied"
            } else {
                "pending"
            };
            println!("  [{}] {}", status, name);
        }
        return Ok(());
    }

    let mut applied_now = 0usize;
    for migration in &migrations {
        let name = migration
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<unknown>")
            .to_string();

        if state.applied.iter().any(|applied| applied == &name) {
            continue;
        }

        let sql = std::fs::read_to_string(migration)
            .into_diagnostic()
            .wrap_err_with(|| format!("Failed to read {}", migration.display()))?;

        if dry_run {
            println!("Would apply {} ({} bytes)", name, sql.len());
        } else {
            println!("Applying {} ({} bytes)", name, sql.len());
            state.applied.push(name);
            applied_now += 1;
        }
    }

    if dry_run {
        println!("✓ Dry run completed");
        return Ok(());
    }

    let encoded = serde_json::to_string_pretty(&state)
        .into_diagnostic()
        .wrap_err("Serialize state")?;
    std::fs::write(&state_file, encoded)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to write {}", state_file.display()))?;

    println!("✓ Applied {} migration(s)", applied_now);
    Ok(())
}

/// Scaffold project templates (wrapper around `new` + template listing).
pub fn scaffold(name: Option<&str>, template: &str, list_templates: bool) -> miette::Result<()> {
    let templates = [
        "bin",
        "lib",
        "web",
        "cli",
        "mcp",
        "ssg",
        "lsp",
        "tool",
        "framework",
        "db-connector",
    ];

    if list_templates {
        println!("Available templates:");
        for t in &templates {
            println!("  - {}", t);
        }
        return Ok(());
    }

    let name = name.unwrap_or("my-eclexia-project");
    new_project(name, template)
}

/// Install dependencies from the project manifest.
pub fn install() -> miette::Result<()> {
    use crate::package::PackageManifest;
    use crate::package_manager::PackageManager;

    // Prefer eclexia.toml for new projects; keep package.toml for compatibility.
    let manifest_path = if Path::new("eclexia.toml").exists() {
        Path::new("eclexia.toml")
    } else {
        Path::new("package.toml")
    };
    if !manifest_path.exists() {
        return Err(miette::miette!(
            "No eclexia.toml (or legacy package.toml) found in current directory.\nRun 'eclexia init' to create a new project."
        ));
    }

    let manifest_content = std::fs::read_to_string(manifest_path)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to read {}", manifest_path.display()))?;

    let manifest: PackageManifest = toml::from_str(&manifest_content)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to parse {}", manifest_path.display()))?;

    // Initialize package manager and install
    let mut pm = PackageManager::new().map_err(|e| miette::miette!("{}", e))?;

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
    let module = codegen
        .generate(&mir_file)
        .map_err(|e| miette::miette!("Code generation failed: {}", e))?;

    // Create VM and debug session
    let vm = eclexia_codegen::VirtualMachine::new(module);
    let mut session = DebugSession::new(vm);

    println!("Eclexia Debugger");
    println!("Type 'help' for commands\n");

    // REPL loop
    loop {
        print!("(eclexia-dbg) ");
        let _ = io::stdout().flush();

        let mut line = String::new();
        if io::stdin().read_line(&mut line).is_err() {
            break;
        }

        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }

        match parts[0] {
            "help" | "h" => {
                println!("Commands:");
                println!("  help, h           - Show this help");
                println!(
                    "  break, b <f> <i>  - Set breakpoint at function index <f>, instruction <i>"
                );
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
            "step" | "s" => match session.step() {
                Ok(()) => println!("{}", session.get_current_instruction()),
                Err(e) => println!("Error: {}", e),
            },
            "continue" | "r" => match session.continue_execution() {
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
            },
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
pub fn doc(
    inputs: &[std::path::PathBuf],
    output_dir: &std::path::Path,
    format: &str,
) -> miette::Result<()> {
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
            eprintln!(
                "Warning: {} has parse errors, documentation may be incomplete",
                input.display()
            );
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
                return Err(miette::miette!(
                    "Unknown format: {}. Use 'html' or 'markdown'",
                    format
                ));
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

/// Watch for file changes and rebuild incrementally.
pub fn watch(path: &Path, debounce_ms: u64) -> miette::Result<()> {
    let debounce = Duration::from_millis(debounce_ms);

    // Determine directory to watch
    let watch_path = if path.is_dir() {
        path.to_path_buf()
    } else {
        path.parent().unwrap_or(Path::new(".")).to_path_buf()
    };

    // Collect initial .ecl files
    let ecl_files: Vec<_> = glob::glob(&format!("{}/**/*.ecl", watch_path.display()))
        .into_diagnostic()?
        .filter_map(|p| p.ok())
        .collect();

    if ecl_files.is_empty() {
        return Err(miette::miette!(
            "No .ecl files found in {}",
            watch_path.display()
        ));
    }

    println!(
        "Watching {} file(s) in {} (debounce: {}ms)",
        ecl_files.len(),
        watch_path.display(),
        debounce_ms
    );
    println!("Press Ctrl+C to stop.\n");

    // Initial compilation
    for file_path in &ecl_files {
        match check_file(file_path) {
            Ok(()) => println!("  ✓ {}", file_path.display()),
            Err(msg) => println!("  ✗ {}: {}", file_path.display(), msg),
        }
    }

    println!("\n--- Watching for changes ---\n");

    // File watcher
    use std::sync::mpsc;
    let (tx, rx) = mpsc::channel::<notify::Event>();

    let mut watcher =
        notify::recommended_watcher(move |res: Result<notify::Event, notify::Error>| {
            if let Ok(event) = res {
                if matches!(
                    event.kind,
                    notify::EventKind::Modify(_)
                        | notify::EventKind::Create(_)
                        | notify::EventKind::Remove(_)
                ) {
                    let _ = tx.send(event);
                }
            }
        })
        .into_diagnostic()
        .wrap_err("Failed to create file watcher")?;

    use notify::Watcher;
    watcher
        .watch(&watch_path, notify::RecursiveMode::Recursive)
        .into_diagnostic()
        .wrap_err_with(|| format!("Failed to watch {}", watch_path.display()))?;

    // Event loop with debouncing
    loop {
        let first_event = rx.recv().into_diagnostic()?;
        let mut changed: std::collections::HashSet<std::path::PathBuf> =
            std::collections::HashSet::new();
        for p in &first_event.paths {
            if p.extension().and_then(|e| e.to_str()) == Some("ecl") {
                changed.insert(p.clone());
            }
        }

        // Debounce window
        let deadline = std::time::Instant::now() + debounce;
        while std::time::Instant::now() < deadline {
            match rx.recv_timeout(debounce) {
                Ok(event) => {
                    for p in &event.paths {
                        if p.extension().and_then(|e| e.to_str()) == Some("ecl") {
                            changed.insert(p.clone());
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => break,
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(miette::miette!("File watcher disconnected"));
                }
            }
        }

        if changed.is_empty() {
            continue;
        }

        let timestamp = chrono_lite_timestamp();
        println!("[{}] {} file(s) changed:", timestamp, changed.len());

        for file_path in &changed {
            match check_file(file_path) {
                Ok(()) => println!("  ✓ {}", file_path.display()),
                Err(msg) => println!("  ✗ {}: {}", file_path.display(), msg),
            }
        }
        println!();
    }
}

/// Check a single file (parse + type check). Returns Ok or error message.
fn check_file(file_path: &Path) -> Result<(), String> {
    let source = std::fs::read_to_string(file_path).map_err(|e| format!("read error: {}", e))?;

    let (file, parse_errors) = eclexia_parser::parse(&source);
    if !parse_errors.is_empty() {
        let msgs: Vec<String> = parse_errors
            .iter()
            .map(|e| e.format_with_source(&source))
            .collect();
        return Err(format!(
            "{} parse error(s):\n    {}",
            parse_errors.len(),
            msgs.join("\n    ")
        ));
    }

    let type_errors = eclexia_typeck::check(&file);
    if !type_errors.is_empty() {
        let msgs: Vec<String> = type_errors
            .iter()
            .map(|e| e.format_with_source(&source))
            .collect();
        return Err(format!(
            "{} type error(s):\n    {}",
            type_errors.len(),
            msgs.join("\n    ")
        ));
    }

    Ok(())
}

/// Simple timestamp without chrono dependency.
fn chrono_lite_timestamp() -> String {
    use std::time::SystemTime;
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default();
    let secs = now.as_secs();
    let hours = (secs / 3600) % 24;
    let minutes = (secs / 60) % 60;
    let seconds = secs % 60;
    format!("{:02}:{:02}:{:02}", hours, minutes, seconds)
}

/// Disassemble an Eclexia source file to show its bytecode.
pub fn disasm(input: &Path) -> miette::Result<()> {
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
        return Err(miette::miette!(
            "Parsing failed with {} errors",
            parse_errors.len()
        ));
    }

    // Type check
    let type_errors = eclexia_typeck::check(&file);
    if !type_errors.is_empty() {
        eprintln!("Type errors:");
        for err in &type_errors {
            eprintln!("  {}", err.format_with_source(&source));
        }
        return Err(miette::miette!(
            "Type checking failed with {} errors",
            type_errors.len()
        ));
    }

    // Lower to HIR -> MIR -> Bytecode
    let hir_file = eclexia_hir::lower_source_file(&file);
    let mir_file = eclexia_mir::lower_hir_file(&hir_file);

    use eclexia_codegen::Backend;
    let mut codegen = eclexia_codegen::BytecodeGenerator::new();
    let module = codegen
        .generate(&mir_file)
        .map_err(|e| miette::miette!("Code generation failed: {}", e))?;

    // Display disassembly
    println!("; Eclexia bytecode disassembly: {}", input.display());
    println!(
        "; {} function(s), {} string(s), {} integer(s), {} float(s)",
        module.functions.len(),
        module.strings.len(),
        module.integers.len(),
        module.floats.len()
    );

    if let Some(entry) = module.entry_point {
        println!("; entry point: function #{}", entry);
    }
    println!();

    // String pool
    if !module.strings.is_empty() {
        println!("; === String Pool ===");
        for (i, s) in module.strings.iter().enumerate() {
            println!(";   [{}] {:?}", i, s);
        }
        println!();
    }

    // Integer pool
    if !module.integers.is_empty() {
        println!("; === Integer Pool ===");
        for (i, n) in module.integers.iter().enumerate() {
            println!(";   [{}] {}", i, n);
        }
        println!();
    }

    // Float pool
    if !module.floats.is_empty() {
        println!("; === Float Pool ===");
        for (i, f) in module.floats.iter().enumerate() {
            println!(";   [{}] {}", i, f);
        }
        println!();
    }

    // Functions
    for (func_idx, func) in module.functions.iter().enumerate() {
        println!("; === Function #{}: {} ===", func_idx, func.name);
        println!(
            ";   params: {}, locals: {}, return: {:?}",
            func.param_count, func.local_count, func.return_ty
        );

        if func.is_adaptive {
            println!(";   [adaptive]");
        }

        if !func.resource_constraints.is_empty() {
            println!(";   constraints:");
            for (name, dim, limit) in &func.resource_constraints {
                println!(";     {} ({:?}) <= {}", name, dim, limit);
            }
        }

        if !func.labels.is_empty() {
            println!(";   labels:");
            for (label, offset) in &func.labels {
                println!(";     {} -> {}", label, offset);
            }
        }

        println!();

        for (offset, instr) in func.instructions.iter().enumerate() {
            let label_marker = func
                .labels
                .iter()
                .find(|(_, &off)| off == offset)
                .map(|(name, _)| format!(" <{}>", name))
                .unwrap_or_default();

            println!(
                "  {:04}{:16} {}",
                offset,
                label_marker,
                format_instruction(instr, &module)
            );
        }

        println!();
    }

    Ok(())
}

/// Format a single bytecode instruction for display.
fn format_instruction(
    instr: &eclexia_codegen::bytecode::Instruction,
    module: &eclexia_codegen::bytecode::BytecodeModule,
) -> String {
    use eclexia_codegen::bytecode::Instruction;

    match instr {
        // Stack
        Instruction::PushInt(n) => format!("push_int       {}", n),
        Instruction::PushFloat(f) => format!("push_float     {}", f),
        Instruction::PushBool(b) => format!("push_bool      {}", b),
        Instruction::PushString(idx) => {
            let s = module
                .strings
                .get(*idx)
                .map(|s| s.as_str())
                .unwrap_or("???");
            format!("push_string    [{}] {:?}", idx, s)
        }
        Instruction::PushUnit => "push_unit".to_string(),
        Instruction::LoadLocal(n) => format!("load_local     %{}", n),
        Instruction::StoreLocal(n) => format!("store_local    %{}", n),
        Instruction::Dup => "dup".to_string(),
        Instruction::Pop => "pop".to_string(),

        // Arithmetic
        Instruction::AddInt => "add_int".to_string(),
        Instruction::SubInt => "sub_int".to_string(),
        Instruction::MulInt => "mul_int".to_string(),
        Instruction::DivInt => "div_int".to_string(),
        Instruction::RemInt => "rem_int".to_string(),
        Instruction::NegInt => "neg_int".to_string(),
        Instruction::AddFloat => "add_float".to_string(),
        Instruction::SubFloat => "sub_float".to_string(),
        Instruction::MulFloat => "mul_float".to_string(),
        Instruction::DivFloat => "div_float".to_string(),
        Instruction::NegFloat => "neg_float".to_string(),

        // Comparison
        Instruction::EqInt => "eq_int".to_string(),
        Instruction::NeInt => "ne_int".to_string(),
        Instruction::LtInt => "lt_int".to_string(),
        Instruction::LeInt => "le_int".to_string(),
        Instruction::GtInt => "gt_int".to_string(),
        Instruction::GeInt => "ge_int".to_string(),
        Instruction::EqFloat => "eq_float".to_string(),
        Instruction::NeFloat => "ne_float".to_string(),
        Instruction::LtFloat => "lt_float".to_string(),
        Instruction::LeFloat => "le_float".to_string(),
        Instruction::GtFloat => "gt_float".to_string(),
        Instruction::GeFloat => "ge_float".to_string(),

        // Logical & bitwise
        Instruction::And => "and".to_string(),
        Instruction::Or => "or".to_string(),
        Instruction::Not => "not".to_string(),
        Instruction::BitAnd => "bit_and".to_string(),
        Instruction::BitOr => "bit_or".to_string(),
        Instruction::BitXor => "bit_xor".to_string(),
        Instruction::Shl => "shl".to_string(),
        Instruction::Shr => "shr".to_string(),
        Instruction::BitNot => "bit_not".to_string(),

        // Exponentiation & range
        Instruction::PowInt => "pow_int".to_string(),
        Instruction::PowFloat => "pow_float".to_string(),
        Instruction::Range => "range".to_string(),
        Instruction::RangeInclusive => "range_incl".to_string(),

        // Control flow
        Instruction::Jump(target) => format!("jump           @{:04}", target),
        Instruction::JumpIf(target) => format!("jump_if        @{:04}", target),
        Instruction::JumpIfNot(target) => format!("jump_if_not    @{:04}", target),
        Instruction::Return => "return".to_string(),
        Instruction::ReturnValue => "return_val".to_string(),

        // Calls
        Instruction::Call(func_idx, argc) => format!("call           fn#{} ({})", func_idx, argc),
        Instruction::CallIndirect(argc) => format!("call_indirect  ({})", argc),
        Instruction::PushFunction(idx) => format!("push_fn        fn#{}", idx),

        // Field/index
        Instruction::FieldAccess(name) => format!("field_access   .{}", name),
        Instruction::SetField(name) => format!("set_field      .{}", name),
        Instruction::IndexAccess => "index_access".to_string(),
        Instruction::SetIndex => "set_index".to_string(),

        // Resources
        Instruction::TrackResource {
            resource,
            dimension,
        } => {
            format!("track_resource {} ({:?})", resource, dimension)
        }
        Instruction::ShadowPriceHook {
            resource,
            dimension,
        } => {
            format!("shadow_hook    {} ({:?})", resource, dimension)
        }

        // Type operations
        Instruction::Cast { from, to } => format!("cast           {:?} -> {:?}", from, to),

        // Debug
        Instruction::DebugPrint => "debug_print".to_string(),
        Instruction::Nop => "nop".to_string(),
        Instruction::CallBuiltin(name, argc) => format!("call_builtin   {} ({})", name, argc),
    }
}

/// Validate interop bridge configurations
pub fn interop_check(command: &str) -> miette::Result<()> {
    use crate::interop::{load_all_bridges, validate_all_bridges};

    let project_root = std::env::current_dir().into_diagnostic()?;
    let interop_dir = project_root.join("interop");

    match command {
        "check" => {
            println!("Validating interop bridge configurations...\n");

            let validations = validate_all_bridges(&interop_dir, &project_root)
                .map_err(|e| miette::miette!("Failed to validate bridges: {}", e))?;

            if validations.is_empty() {
                println!(
                    "No bridge configurations found in {}",
                    interop_dir.display()
                );
                return Ok(());
            }

            let mut all_valid = true;

            for validation in &validations {
                println!("Bridge: {}", validation.bridge_name);
                println!(
                    "  Status: {}",
                    if validation.valid {
                        "✓ Valid"
                    } else {
                        "✗ Invalid"
                    }
                );

                if !validation.errors.is_empty() {
                    all_valid = false;
                    println!("  Errors:");
                    for error in &validation.errors {
                        println!("    - {}", error);
                    }
                }

                if !validation.warnings.is_empty() {
                    println!("  Warnings:");
                    for warning in &validation.warnings {
                        println!("    - {}", warning);
                    }
                }

                println!();
            }

            if all_valid {
                println!("All {} bridge(s) are valid!", validations.len());
            } else {
                return Err(miette::miette!("Some bridges have errors"));
            }
        }
        "list" => {
            println!("Loading bridge configurations...\n");

            let bridges = load_all_bridges(&interop_dir)
                .map_err(|e| miette::miette!("Failed to load bridges: {}", e))?;

            if bridges.is_empty() {
                println!(
                    "No bridge configurations found in {}",
                    interop_dir.display()
                );
                return Ok(());
            }

            println!("Found {} bridge configuration(s):\n", bridges.len());

            for (name, bridge) in &bridges {
                println!("  {} → {}", name, bridge.language.name);
                println!("    Repo: {}", bridge.language.repo);
                println!("    Build: {}", bridge.language.build_system);
                println!("    FFI: {}", bridge.language.ffi_mechanism);
                if let Some(ref header) = bridge.bridge.header {
                    println!("    Header: {}", header);
                }
                if let Some(ref target) = bridge.bridge.target_file {
                    println!("    Target: {}", target);
                }
                println!();
            }
        }
        _ => {
            return Err(miette::miette!(
                "Unknown interop command: '{}'. Use 'check' or 'list'",
                command
            ));
        }
    }

    Ok(())
}
