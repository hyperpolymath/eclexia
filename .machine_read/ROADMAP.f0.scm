;; SPDX-License-Identifier: PMPL-1.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; ROADMAP.f0.scm — Machine-readable development roadmap (Phase F0)

(define-module (eclexia machine-read roadmap)
  #:export (roadmap current-phase milestones dependencies))

(define roadmap
  '((schema . "hyperpolymath.roadmap/1")
    (repo . "hyperpolymath/eclexia")
    (phase . "f0")
    (phase-name . "Foundation")
    (last-updated . "2026-01-01")))

(define current-phase
  '((id . "f0")
    (name . "Foundation Phase")
    (status . "in-progress")
    (completion . 55)
    (objectives
      . ("Complete core compiler pipeline"
         "Establish type checking with dimensional analysis"
         "Implement shadow price runtime selection"
         "Create reference interpreter"))))

(define milestones
  '((m0-lexer
      . ((status . "complete")
         (deliverables . ("Token types" "Dimensional literals" "Position tracking"))))

    (m1-parser
      . ((status . "complete")
         (deliverables . ("Recursive descent parser" "AST construction" "Error recovery"))))

    (m2-ast
      . ((status . "complete")
         (deliverables . ("Expression types" "Type annotations" "Dimensional type nodes"))))

    (m3-typeck
      . ((status . "in-progress")
         (completion . 60)
         (deliverables . ("Hindley-Milner inference" "Dimensional type checking" "Error messages"))
         (remaining . ("Full dimensional unification" "Constraint solving" "Energy bound inference"))))

    (m4-hir
      . ((status . "not-started")
         (deliverables . ("High-level IR" "Desugaring" "Name resolution"))))

    (m5-mir
      . ((status . "not-started")
         (deliverables . ("Mid-level IR" "Optimization passes" "Shadow price analysis"))))

    (m6-codegen
      . ((status . "not-started")
         (deliverables . ("LLVM backend" "WebAssembly target" "Energy instrumentation"))))

    (m7-runtime
      . ((status . "not-started")
         (completion . 5)
         (deliverables . ("Shadow price runtime" "Energy metering" "Adaptive dispatch"))))))

(define dependencies
  '((m3-typeck . (m0-lexer m1-parser m2-ast))
    (m4-hir . (m3-typeck))
    (m5-mir . (m4-hir))
    (m6-codegen . (m5-mir))
    (m7-runtime . (m6-codegen))))
