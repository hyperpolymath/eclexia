<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

[![OpenSSF Best Practices](https://img.shields.io/badge/OpenSSF-Best_Practices-green?logo=opensourcesecurity)](https://www.bestpractices.dev/en/projects/new?repo_url=https://github.com/hyperpolymath/eclexia)
[![License: PMPL-1.0](https://img.shields.io/badge/License-MPL--2.0-blue.svg)](https://github.com/hyperpolymath/palimpsest-license) <embed
src="https://api.thegreenwebfoundation.org/greencheckimage/github.com"
data-link="https://www.thegreenwebfoundation.org/green-web-check/?url=github.com" />

Eclexia is an Economics-as-Code programming language. It treats energy,
time, memory, and carbon as first-class constraints so software can
optimize for performance and sustainability together.

# Quick Links

- [Getting Started](GETTING_STARTED.md)

- [Current Implementation Status](QUICK_STATUS.md)

- [Documentation Index](docs/README.md)

- [Wiki Home](docs/wiki/Home.md)

- [Language Specification](SPECIFICATION.md)

- [Whitepaper](WHITEPAPER.md)

- [Formal Proofs](PROOFS.md)

- [Implementation Roadmap](IMPLEMENTATION_ROADMAP.md)

- [Contributing](CONTRIBUTING.md)

- [Security Policy](SECURITY.md)

# What Is Eclexia?

Eclexia introduces economics directly into language semantics:

- Resource-aware constraints in code (`@requires`, `@provides`)

- Adaptive solution selection under changing runtime conditions

- Shadow-price-based tradeoff decisions

- Carbon-aware execution and scheduling

- Multi-objective optimization declared at source level

Example shape of an adaptive function:

```eclexia
adaptive def matrix_multiply(A: Matrix, B: Matrix) -> Matrix
    @requires: energy < 100J, latency < 500ms
    @optimize: minimize energy, minimize carbon
{
    @solution "gpu_accelerated":
        @when: gpu_available && matrix_size > 1000
        @provides: energy: 50J, latency: 100ms, carbon: 5gCO2e
    {
        gpu::multiply(A, B)
    }

    @solution "parallel_cpu":
        @when: cpu_cores >= 4
        @provides: energy: 80J, latency: 300ms, carbon: 8gCO2e
    {
        parallel::multiply(A, B)
    }
}
```

# Quick Start

```bash
# Build from source (Rust 1.75+)
cargo build --release

# Run tests
cargo test --workspace

# Run a sample program
cargo run -- run examples/hello.ecl
```

Compiler binary:

```text
target/release/eclexia
```

For a fuller walkthrough, use
<a href="GETTING_STARTED.md" class="md">GETTING_STARTED</a>.

# Documentation Index

| Document | Purpose | Audience |
|----|----|----|
| [Getting Started](GETTING_STARTED.md) | Installation, first run, and CLI usage | New users |
| [Quick Status](QUICK_STATUS.md) | Snapshot of what works and what does not | Users and contributors |
| [Specification](SPECIFICATION.md) | Language syntax and semantics | Language implementers |
| [Whitepaper](WHITEPAPER.md) | High-level design and motivation | General and research audience |
| [Proofs](PROOFS.md) | Formal statements and theorem development | Researchers |
| [Formal Verification](FORMAL_VERIFICATION.md) | Coq/Agda proof status and verification notes | Researchers and maintainers |
| [Implementation Roadmap](IMPLEMENTATION_ROADMAP.md) | Medium/long-term engineering roadmap | Contributors and maintainers |
| [Toolchain Status](TOOLCHAIN_STATUS.md) | Status of compiler/runtime/tooling components | Contributors |
| [Algorithms](ALGORITHMS.md) | Algorithmic details and implementation notes | Contributors and researchers |
| [Bibliography](BIBLIOGRAPHY.md) | Research references used by the project | Researchers |

# Current Status

As of <a href="QUICK_STATUS.md" class="md">QUICK_STATUS</a> (updated
2026-02-12):

- Alpha stage

- Core compiler pipeline functional

- Runtime components available with active development

- Conformance and workspace tests are in regular use

This repository has many deep-dive documents. The README now stays
focused on orientation, while detailed operational and research content
lives in dedicated docs and wiki pages.

# Repository Layout

```text
eclexia/
├── README.adoc
├── compiler/          # compiler crates and CLI front-end
├── runtime/           # runtime crates (scheduler, profiling, carbon, shadow)
├── libraries/         # ecosystem libraries
├── stdlib/            # standard library sources
├── examples/          # sample .ecl programs
├── tests/             # conformance and integration tests
├── formal/            # Coq/Agda artifacts
└── docs/              # reference docs, tutorials, and generated docs
```

# README vs Wiki

The README should remain a concise project entry point. Long-lived
narrative and frequently evolving content is better placed in the wiki.

Recommended wiki destinations:

- Architecture walkthroughs and subsystem maps

- Backlog triage and milestone notes

- Design discussions and ADR-style rationale

- Research notes and reading guides

- Contributor onboarding playbooks

Proposed wiki structure and migration map:
[docs/wiki/README.md](docs/wiki/README.md)

# Contributing

- [Contributing Guide](CONTRIBUTING.md)

- [Code of Conduct](CODE_OF_CONDUCT.md)

- [Security Policy](SECURITY.md)

# License

Eclexia is licensed under MPL-2.0. See [LICENSE](LICENSE) and
<a href="LICENSE.txt" class="txt">LICENSE</a>.

# Contact

- General: [[info@eclexia.org](info@eclexia.org)](info@eclexia.org)

- Research:
  [[research@eclexia.org](research@eclexia.org)](research@eclexia.org)

- Security:
  [[security@eclexia.org](security@eclexia.org)](security@eclexia.org)

Repository: <https://gitlab.com/eclexia-lang/eclexia>

# Mission

Make resource-efficient, carbon-aware software the default, not the
exception.
