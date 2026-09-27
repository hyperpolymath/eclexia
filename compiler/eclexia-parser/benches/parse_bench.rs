// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Parser throughput benchmarks.
//!
//! Addresses the standing Known-Gap "no measured benchmarks (all performance
//! claims are projections)" for the compiler front end. `cargo bench` produces
//! real wall-clock numbers; the `bench.yml` workflow runs it on CI hardware
//! weekly and on demand so claims can cite a measurement instead of a guess.

use std::hint::black_box;
use std::path::PathBuf;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

/// Any non-zero-size input so the benchmark never measures the empty case.
const FALLBACK_SOURCE: &str = "def main() -> Unit { println(\"hello\") }\n";

fn corpus() -> Vec<(String, String)> {
    let mut files: Vec<(String, String)> = Vec::new();
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.pop(); // compiler/
    dir.pop(); // repo root
    dir.push("examples");

    let mut entries: Vec<PathBuf> = std::fs::read_dir(&dir)
        .map(|rd| {
            rd.filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "ecl"))
                .collect()
        })
        .unwrap_or_default();
    entries.sort();

    for path in &entries {
        if let Ok(text) = std::fs::read_to_string(path) {
            files.push((path.file_name().unwrap().to_string_lossy().into_owned(), text));
        }
    }

    if files.is_empty() {
        // Keep the benchmark runnable from any checkout shape.
        files.push(("fallback.ecl".to_string(), FALLBACK_SOURCE.to_string()));
    }
    files
}

fn bench_parse_corpus(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser");
    for (name, text) in corpus() {
        let id = BenchmarkId::new("parse", name);
        // Throughput in input bytes/sec so CI numbers are comparable over time.
        group.throughput(criterion::Throughput::Bytes(text.len() as u64));
        group.bench_with_input(id, &text, |b, src| {
            b.iter(|| {
                let (ast, errors) = eclexia_parser::parse(black_box(src));
                black_box((ast, errors));
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_parse_corpus);
criterion_main!(benches);
