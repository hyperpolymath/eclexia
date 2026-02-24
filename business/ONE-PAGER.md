# Eclexia One-Pager

## What Eclexia Is
Eclexia is a programming language and runtime for **economics-as-code**: developers declare resource budgets (energy, time, memory, carbon), and the system verifies constraints and chooses low-cost execution strategies.

## Problem
Modern software teams cannot reliably answer:
- How much energy and carbon this feature consumes.
- Which implementation is economically optimal under real constraints.
- Whether runtime behavior stays within declared budgets.

This creates operational risk, regulatory exposure, and escalating cloud costs.

## Solution
Eclexia provides:
- Resource-aware language features (`@requires`, adaptive functions, shadow prices).
- Runtime tracking of energy/time/memory/carbon.
- Decision support via shadow-price-based selection.
- Verification-oriented tooling (conformance tests, formal methods roadmap).

## Why Now
- Carbon accountability is moving from voluntary to contractual.
- AI and data workloads are driving compute and power costs up.
- Organizations need software-level controls, not only infra dashboards.

## Target Users
- Platform engineering teams with strict cost and reliability requirements.
- Sustainability and FinOps teams needing enforceable technical controls.
- Research and regulated sectors (public sector, universities, industrial IoT).

## Product Paths
- Open source language + runtime.
- Hosted control plane for runtime metrics and policy governance.
- Enterprise support, training, and integration services.

## Differentiation
- Budgets are first-class in the language, not bolted-on observability.
- Adaptive selection ties runtime decisions to explicit economic models.
- Carbon and resource constraints are integrated into compile/runtime workflow.

## Current State (February 11, 2026)
- Core compiler/runtime foundation is in place.
- Dedicated `eclexia-carbon` and `eclexia-shadow` crates added and verified.
- Conformance and integration test suites are operational.
- Website/playground and business rollout are active workstreams.

## Ask
- Funding and partnerships to accelerate:
  1. Web playground + onboarding.
  2. Enterprise-facing ecosystem libraries.
  3. Pilot deployments with measurable carbon/cost reduction.
