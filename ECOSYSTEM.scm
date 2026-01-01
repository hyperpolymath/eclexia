;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ECOSYSTEM.scm — eclexia

(ecosystem
  (version "1.1.0")
  (name "eclexia")
  (type "language")
  (purpose "Energy-aware programming language with dimensional types and shadow price optimization")

  (position-in-ecosystem
    "Canonical upstream for Eclexia language. Part of hyperpolymath ecosystem. Follows RSR guidelines.")

  (anchor-system
    (authority "upstream-canonical")
    (anchor-file "./ANCHOR.scm")
    (machine-read-dir "./.machine_read/")
    (satellite-policy "Downstream repos must pin to this upstream and cannot redefine semantics."))

  (related-projects
    (project (name "rhodium-standard-repositories")
             (url "https://github.com/hyperpolymath/rhodium-standard-repositories")
             (relationship "standard"))
    (project (name "eclexia-playground")
             (url "https://github.com/hyperpolymath/eclexia-playground")
             (relationship "downstream-satellite"))
    (project (name "eclexia-vscode")
             (url "https://github.com/hyperpolymath/eclexia-vscode")
             (relationship "downstream-tooling"))
    (project (name "eclexia-docs")
             (url "https://github.com/hyperpolymath/eclexia-docs")
             (relationship "downstream-documentation")))

  (what-this-is
    "Authoritative source for Eclexia language semantics, specification, and compiler implementation.")

  (what-this-is-not
    "- NOT exempt from RSR compliance"
    "- NOT a playground or demo repository (see eclexia-playground)"
    "- NOT where IDE plugins live (see eclexia-vscode)"))
