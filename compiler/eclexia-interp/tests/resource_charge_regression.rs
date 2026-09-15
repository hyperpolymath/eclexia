// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Regression tests for ADR-001 section 2.2.1: `@requires` must never be
//! charged to a caller as if it were a cost.
//!
//! Before the fix, `Interpreter::call_value_inner`'s plain-`def`/`fn` path
//! added the callee's *declared* `@requires` energy ceiling to the caller's
//! running total up front (`self.energy_used += limit`), regardless of what
//! the callee's body actually did. `@provides` is the only source of a
//! charge; `@requires` is a budget the callee's own body promises not to
//! exceed. See `docs/adr/ADR-001-effects-and-unbounded-resource-accounting.adoc`,
//! section 2.2.1 ("`@requires` is charged as if it were a cost, on one path
//! only").

fn run_source(source: &str) -> eclexia_interp::RuntimeResult<eclexia_interp::Value> {
    let (file, errors) = eclexia_parser::parse(source);
    assert!(
        errors.is_empty(),
        "fixture failed to parse: {:?}",
        errors
    );
    eclexia_interp::run(&file)
}

/// A callee whose body does no work and declares no `@provides` must cost
/// its caller nothing, no matter how tight its own `@requires` ceiling is.
/// Two calls that would overflow the caller's budget under the old
/// point-charge behaviour (2 * 80J = 160J > 100J) must now succeed, because
/// the callee's actual measured consumption is 0J each time.
#[test]
fn requires_ceiling_is_not_charged_to_caller() {
    let source = r#"
        def callee() -> Int
            @requires: energy < 80J
        {
            1
        }

        def caller() -> Int
            @requires: energy < 100J
        {
            callee() + callee()
        }

        fn main() {
            caller();
        }
    "#;

    let result = run_source(source);
    assert!(
        result.is_ok(),
        "expected success once @requires stops being charged as a cost, got: {:?}",
        result
    );
}

/// Positive control: a genuine `@provides` cost on an adaptive solution
/// must still be charged to the caller, and must still be able to trip a
/// `ResourceViolation` when it overflows the caller's own `@requires`
/// budget. This guards against a fix that accidentally stops charging
/// anything at all.
#[test]
fn provides_cost_still_triggers_violation() {
    let source = r#"
        adaptive def heavy() -> Int
        {
            @solution "only":
                @when: true
                @provides: energy: 150J
            {
                1
            }
        }

        def caller() -> Int
            @requires: energy < 100J
        {
            heavy()
        }

        fn main() {
            caller();
        }
    "#;

    let result = run_source(source);
    assert!(
        result.is_err(),
        "expected a ResourceViolation: @provides(150J) exceeds caller's @requires(100J), got: {:?}",
        result
    );
    let err = result.unwrap_err();
    let message = format!("{}", err);
    assert!(
        matches!(err, eclexia_interp::RuntimeError::ResourceViolation { .. }),
        "expected ResourceViolation, got: {}",
        message
    );
}
