<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) -->

# Next-session prompt — eclexia (drafted 2026-06-19T21:38:41Z)

Copy the block below and give it to the next Claude session.

---

You are picking up **eclexia** (`hyperpolymath/eclexia`) — *Economics-as-Code*: a
resource-typed, Rust-implemented language that prices what programs give up
(energy / time / carbon + **structured information loss** via the `Echo[A,B]` type
former, erasure priced by Landauer's principle).

**Read first (authoritative current state):** `AFFIRMATION.adoc` (root),
`.machine_readable/6a2/STATE.a2ml`, and
`.machine_readable/contractiles/{Mustfile,Intentfile}.a2ml`.
Phase **alpha / 77%**; 25 crates, 519 tests green, zero clippy; Coq+Agda
metatheory compiles (`EchoThermo.v` is axiom-free). Echo is **core** — in the
type system *and* the resource economy. Do not treat the Feb-2026 CLAUDE.md
status as current; STATE.a2ml supersedes it.

**Gates (must hold before *and* after any change):** `cargo build --workspace`
and `make -C formal/coq` pass; `must check` (Mustfile) green; MPL-2.0 SPDX on
every new file. Dev branch `claude/<slug>`; draft PRs; CI green before merge.
**Ask before** changing language semantics (`THEORY.md`, `SPECIFICATION.md`),
the `formal/` Coq/Agda metatheory, or `ANCHOR.scm`.

**The work — pick ONE committed Intent (all currently `declared`):**

1. **`echo-functor`** — add functorial `echo_map` + (graded co)functor laws as
   conformance tests (`tests/conformance/valid/echo_map.ecl`). Builds on the
   `Echo[A,B]` type former + `landauer_cost` bridge (#32).
   *Highest leverage: extends the headline Echo feature with checkable laws;
   self-contained; no metatheory risk.*
2. **`landauer-real-valued`** — lift `EchoThermo.v`'s discrete shadow toward
   real-valued `k·T·ln2` and connect to `ShadowPrices.v`.
   *Touches the Coq metatheory — ask before editing `formal/`.*
3. **`wasm-gc`** — wire the WASM bump allocator (currently defined-not-wired) so
   linear memory has GC. *Closes an honest known gap; work in `eclexia-wasm`.*
4. **`llvm-linking`** — automate linking to the `rt-native` static library
   (currently manual). *Closes an honest known gap; `eclexia-llvm` + build glue.*

**Recommended start:** `echo-functor` (extends the core Echo story, conformance-
test shaped, zero metatheory risk) — or `wasm-gc` if you'd rather close a
concrete backend gap.

**On finish:** update `STATE.a2ml` `route-to-mvp` + flip the Intent's status
(`declared` → `in_progress`/`done`); refresh `AFFIRMATION.adoc`'s timestamp and
tables; keep the known-gaps list honest.

**Wishes (NOT now):** `measured-benchmarks` (near); `os-metrics`,
`registry-deploy` (mid); unified `shadow-price ↔ Echo` LP model (far).

---

_Provenance: generated from STATE.a2ml (2026-06-13), the contractiles, and
`main@afc1a9a`. See `AFFIRMATION.adoc` for the full Must/Intend/Wish tables._
