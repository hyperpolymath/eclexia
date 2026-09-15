// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Integration tests for `eclexia verify` (ADR-001 Gate 0).
//!
//! These drive the real `eclexia` binary end-to-end rather than calling
//! library functions directly, so they exercise the exact CLI contract
//! (exit codes, `--format=json` shape) that ADR-001 (ii) specifies and that
//! CI depends on.

use std::path::Path;
use std::process::{Command, Output};

fn eclexia_bin() -> Command {
    match std::env::var("CARGO_BIN_EXE_eclexia") {
        Ok(exe_path) => Command::new(exe_path),
        Err(_) => {
            let mut cmd = Command::new("cargo");
            cmd.args(["run", "-q", "--"]);
            cmd
        }
    }
}

fn run_verify(fixture: &str, unknown: &str, format: &str) -> Output {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(fixture);
    eclexia_bin()
        .arg("verify")
        .arg(&path)
        .arg("--unknown")
        .arg(unknown)
        .arg("--format")
        .arg(format)
        .output()
        .expect("failed to execute eclexia verify")
}

fn verdict_of<'a>(json: &'a serde_json::Value, function: &str, resource: &str) -> &'a str {
    json["verdicts"]
        .as_array()
        .expect("verdicts array")
        .iter()
        .find(|v| v["function"] == function && v["resource"] == resource)
        .unwrap_or_else(|| panic!("no verdict for {function}.{resource}: {json}"))["verdict"]
        .as_str()
        .expect("verdict string")
}

/// ADR-001 Gate 0b exit test: a paired over-limit/under-limit fixture must
/// produce `Disproved` (with non-zero exit) for the over-limit solution and
/// `Proved` for the under-limit one. Neither an always-Proved nor an
/// always-Unknown verifier can pass this.
#[test]
fn gate0b_paired_fixture_disproves_over_limit_and_proves_under_limit() {
    let output = run_verify("adaptive_budget_paired.ecl", "fail", "json");
    let json: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("bad JSON ({e}): {}", String::from_utf8_lossy(&output.stdout)));

    assert_eq!(
        verdict_of(&json, "compute_fast", "energy"),
        "proved",
        "50J under a 100J budget must be Proved"
    );
    assert_eq!(
        verdict_of(&json, "compute_slow", "energy"),
        "disproved",
        "200J over a 100J budget must be Disproved"
    );

    // Disproved takes precedence in the exit code (ADR-001 (ii)): exit 1,
    // even though `compute` (the dispatch wrapper) is separately Unknown.
    assert_eq!(
        output.status.code(),
        Some(1),
        "a Disproved verdict must exit 1 regardless of --unknown policy"
    );
}

/// Negative control: raise the budget above both solutions. Both must
/// report Proved, and — since nothing is Disproved or Unknown-under-fail
/// left — the process must exit 0 under `--unknown=warn`. The dispatch
/// wrapper (`compute`) is still Unknown (G3b builds real dispatch; G0b only
/// emits per-solution evidence), so this specifically drives `warn`, not
/// `fail`, to isolate the wrapper's honest ceiling from the two solutions'
/// real verdicts.
#[test]
fn gate0b_negative_control_proves_both_solutions() {
    let output = run_verify("adaptive_budget_negative_control.ecl", "warn", "json");
    let json: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("bad JSON ({e}): {}", String::from_utf8_lossy(&output.stdout)));

    assert_eq!(verdict_of(&json, "compute_fast", "energy"), "proved");
    assert_eq!(verdict_of(&json, "compute_slow", "energy"), "proved");
    assert_eq!(
        verdict_of(&json, "compute", "energy"),
        "unknown",
        "the dispatch wrapper carries no ResourceTrack evidence until G3b"
    );

    assert_eq!(
        output.status.code(),
        Some(0),
        "no Disproved and --unknown=warn must exit 0 even with the wrapper's Unknown"
    );
}

/// The same negative-control fixture under `--unknown=fail` must exit 2:
/// the wrapper's honest Unknown is real inconclusive evidence, and a
/// failing policy must not let it slide silently to exit 0.
#[test]
fn gate0b_negative_control_wrapper_unknown_fails_under_strict_policy() {
    let output = run_verify("adaptive_budget_negative_control.ecl", "fail", "json");
    assert_eq!(output.status.code(), Some(2));
}

/// ADR-001 section 1, T4 (per-resource coverage): a resource that is
/// constrained but never `@provides`-tracked by any solution must report
/// Unknown for that resource specifically, without disturbing the verdict
/// for a resource that *is* tracked.
#[test]
fn gate0_untracked_resource_reports_unknown_independently() {
    let output = run_verify("adaptive_untracked_resource.ecl", "warn", "json");
    let json: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("bad JSON ({e}): {}", String::from_utf8_lossy(&output.stdout)));

    assert_eq!(verdict_of(&json, "compute_only", "energy"), "proved");
    assert_eq!(verdict_of(&json, "compute_only", "carbon"), "unknown");
}
