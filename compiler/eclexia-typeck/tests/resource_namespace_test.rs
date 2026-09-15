// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! ADR-001 Gate 1: resource/parameter namespace split.
//!
//! Resource names declared in `@requires`, `@provides`, and `@optimize`
//! clauses occupy a namespace separate from term variables (function
//! parameters and locals). A name that appears in both positions must
//! be rejected with a `TypeError::ResourceNamespaceCollision`
//! diagnostic rather than silently resolved as one or the other, and
//! a resource name must never be visible as an ordinary identifier
//! inside a function body. Both plain (`def`) and adaptive
//! (`adaptive def`) functions must agree on this.
//!
//! See docs/adr/ADR-001-effects-and-unbounded-resource-accounting.adoc,
//! section "Resource names and term variables share one namespace, and
//! the two function kinds disagree".

use eclexia_parser::Parser;
use eclexia_typeck::TypeError;

/// Parse `source` and run the type checker, panicking on a parse
/// failure (a parse error would mean the fixture itself is malformed,
/// which is a test-authoring bug, not something under test here).
fn check_source(source: &str) -> Vec<TypeError> {
    let mut parser = Parser::new(source);
    let (ast, parse_errors) = parser.parse_file();
    assert!(
        parse_errors.is_empty(),
        "fixture failed to parse: {:?}",
        parse_errors
    );
    eclexia_typeck::check(&ast)
}

fn has_collision(errors: &[TypeError], expected_name: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            TypeError::ResourceNamespaceCollision { name, .. } if name == expected_name
        )
    })
}

fn has_mismatch(errors: &[TypeError]) -> bool {
    errors
        .iter()
        .any(|e| matches!(e, TypeError::Mismatch { .. }))
}

fn has_undefined(errors: &[TypeError], expected_name: &str) -> bool {
    errors.iter().any(|e| {
        matches!(
            e,
            TypeError::Undefined { name, .. } if name == expected_name
        )
    })
}

// Case 1: a plain `def` parameter named `energy` collides with an
// `@requires: energy < ...` resource declaration on the same
// function. Must be rejected via ResourceNamespaceCollision, and
// (because the parameter keeps its declared `Float` type rather than
// being shadowed) must NOT also produce an incidental Mismatch.
#[test]
fn plain_def_param_collides_with_requires_resource() {
    let source = r#"
        def f(energy: Float) -> Float
            @requires: energy < 1J
        {
            g(energy)
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        has_collision(&errors, "energy"),
        "expected a ResourceNamespaceCollision for 'energy', got: {:?}",
        errors
    );
    assert!(
        !has_mismatch(&errors),
        "collision must not also produce an incidental type Mismatch, got: {:?}",
        errors
    );
}

// Case 2 (negative control): renaming the parameter away from the
// resource name removes the collision entirely — zero errors.
#[test]
fn plain_def_renamed_param_is_accepted() {
    let source = r#"
        def f(joules: Float) -> Float
            @requires: energy < 1J
        {
            g(joules)
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        errors.is_empty(),
        "renamed parameter must type-check cleanly, got: {:?}",
        errors
    );
}

// Case 3 (negative control): a parameter named `energy` is legal on
// its own — the collision only exists when the SAME function also
// declares `energy` as a resource. Zero errors.
#[test]
fn plain_def_param_named_energy_without_requires_is_accepted() {
    let source = r#"
        def f(energy: Float) -> Float {
            g(energy)
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        errors.is_empty(),
        "a parameter merely named 'energy' with no @requires must be legal, got: {:?}",
        errors
    );
}

// Case 4: the same collision as case 1, but on an `adaptive def`.
// Before this fix, check_adaptive_function performed no injection
// AND no collision check, so this was silently ACCEPTED — the exact
// asymmetry the ADR calls out between the two function kinds. It
// must now be rejected with the same diagnostic as case 1.
#[test]
fn adaptive_def_param_collides_with_requires_resource() {
    let source = r#"
        adaptive def f(energy: Float) -> Float
            @requires: energy < 1J
        {
            @solution "only":
                @when: true
            {
                g(energy)
            }
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        has_collision(&errors, "energy"),
        "adaptive def must reject the same collision as plain def, got: {:?}",
        errors
    );
}

// Case 5: the collision surface via a per-solution `@provides`
// declaration rather than a function-level `@requires` constraint.
// No @requires appears at all, so a collision here can only come
// from the provides-name collection path.
#[test]
fn adaptive_def_param_collides_with_provides_resource() {
    let source = r#"
        adaptive def f(energy: Float) -> Float {
            @solution "only":
                @when: true
                @provides: energy: 1J
            {
                g(energy)
            }
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        has_collision(&errors, "energy"),
        "a @provides resource name colliding with a parameter must be rejected, got: {:?}",
        errors
    );
}

// Case 6: the collision surface via the paren-form `@requires(...)`
// annotation attribute (as opposed to the colon-form constraint used
// in cases 1 and 4).
#[test]
fn plain_def_param_collides_with_paren_form_requires_attribute() {
    let source = r#"
        @requires(energy: 1J)
        def f(energy: Float) -> Float {
            g(energy)
        }

        def g(x: Float) -> Float {
            x
        }
    "#;

    let errors = check_source(source);
    assert!(
        has_collision(&errors, "energy"),
        "paren-form @requires(...) must feed the same collision check, got: {:?}",
        errors
    );
}

// Case 7: resource names are never visible as ordinary body
// identifiers. Before this fix, `check_function` injected `energy`
// into the body scope as a Ty::Resource binding, so a function with
// NO parameter named `energy` could still reference the bare
// identifier `energy` inside its body and have it silently resolve.
// After the fix this must be Undefined — the "never in a function
// body" half of the ADR ruling. Without this test, a mutant that adds
// the collision check but leaves the old injection in place would
// pass every other test in this file.
#[test]
fn resource_name_is_not_visible_as_a_body_identifier() {
    let source = r#"
        def f(n: Int) -> Int
            @requires: energy < 1J
        {
            let _ = energy;
            n
        }
    "#;

    let errors = check_source(source);
    assert!(
        has_undefined(&errors, "energy"),
        "a resource name must be Undefined inside the function body, got: {:?}",
        errors
    );
}
