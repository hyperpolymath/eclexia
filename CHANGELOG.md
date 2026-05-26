<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Changelog

All notable changes to `eclexia` will be documented in this file.

This file is generated from conventional commits by the
[`changelog-reusable.yml`](https://github.com/hyperpolymath/standards/blob/main/.github/workflows/changelog-reusable.yml)
workflow (`hyperpolymath/standards#206`). Adopt the workflow in this repo's CI to keep this file in sync automatically — see
[`templates/cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml)
for the canonical config.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
this project aims to follow [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- feat: implement S-expression and JSON AST dump for parse command
- feat: add DAP support for eclexia
- feat: add AST visitor framework (eclexia-ast::visitor)
- feat: add parse command for AST visualization (eclexia parse)

### Fixed

- fix(ci): sync hypatia-scan.yml to canonical (413: env.HOME+Phase-2+SARIF) (#15)
- fix(ci): adopt canonical hypatia-scan.yml (env.HOME/scanner-layout + Comment-step gate) (#12)
- fix(ci): move secret-scanner Cargo.toml gate from job-level if: to step-level (#10)
- fix: ShadowPrices.v compiles clean, MIR macro expansion emits runtime intrinsic
- fix: repair broken crates and implement concurrency/array stubs
- fix(formal): resolve 3 Idris2 proof holes in Layout.idr
- fix(formal): resolve Agda hole in ResourceTracking.agda
- fix: seam audit — SPDX headers, copyright lines, consistency fixes

### Documentation

- docs(readme): add SPDX header, OSSF and GWF badges

### CI

- build(deps): Bump actions/checkout in the actions group (#18)
- build(deps): Bump the actions group with 3 updates (#17)
- build(deps): Bump the actions group across 1 directory with 3 updates (#13)
- ci: bump actions/upload-artifact SHA to current v4 (#9)
- ci: fix workflow-linter YAML parse error + self-flag bug

## Pre-history

Prior commits to this file's introduction are recorded in git history but not formally classified into Keep-a-Changelog sections. To backfill, run `git cliff -o CHANGELOG.md` locally using the canonical [`cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml) — this is one-shot mechanical work.

---

<!-- This file was seeded by the 2026-05-26 estate tech-debt audit follow-up (Row-2 Phase 3); see [`hyperpolymath/standards/docs/audits/2026-05-26-estate-documentation-debt.md`](https://github.com/hyperpolymath/standards/blob/main/docs/audits/2026-05-26-estate-documentation-debt.md). -->
