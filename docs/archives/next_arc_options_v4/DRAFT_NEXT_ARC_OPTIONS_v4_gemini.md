# Draft Next Arc Options v4 (Post vNext+16 Planning)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft only (not frozen).
Goal: define post-`vNext+16` options and identify the concrete first slice for `vNext+17`.

## Consolidation Note

For post-`vNext+16` planning, this file remains the working source of truth.
`docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` remains historical context only.

## Baseline Snapshot (Post vNext+16)

Current baseline includes:

- `vNext+15` (`C1`-`C4`) complete:
  - deterministic lane-reporting and evidence-only projection extraction alignment.
- `vNext+16` (`D1`-`D4`) complete and merged on `main`:
  - deterministic dangling-reference diagnostics (D1).
  - dependency-cycle policy diagnostics (D2).
  - minimal deontic conflict checks (D3).
  - manifest-driven integrity coverage and transfer report (D4).
- v16 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `artifact_dangling_reference_determinism_pct=100.0`
  - `artifact_cycle_policy_determinism_pct=100.0`
  - `artifact_deontic_conflict_determinism_pct=100.0`
- prior arc guarantees remain green:
  - all stop-gate tracked `vNext+6` through `vNext+15` metrics remain at threshold.
  - core-ir depth transfer report tracking remains stable.

Net: Formal integrity hardening is complete, ensuring structural safety. The foundation is now resilient enough to handle deeper diagnostic resolution or cautious semantic expansion.

## Repo-Grounded Clarifications

1. Integrity artifacts function as defense-in-depth:
   - v16 established deterministic checks that run *before* strict canonical `adeu_core_ir@0.1` model-validation.
2. Several diagnostic expansions were intentionally deferred:
   - v15 deferred span, label, and score mismatches.
   - v16 deferred `permitted` modality checks and `excepts`-edge conflict suppression.
3. Next arc can selectively finish these deferred diagnostics, or finally pivot to careful semantic expansion.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance paths.
- Runtime behavior must emit evidence events in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- New artifacts must be schema-versioned and canonically serialized.
- Stop-gate schema continuity remains additive on `stop_gate_metrics@1` unless explicitly re-locked.

## Path 10a: Extraction Fidelity Diagnostics (v15 Follow-on)

### Goal

Complete the v15 projection alignment diagnostics by evaluating text, span, and multiplicity bounds.

### Scope

1. Implement the deferred `label_text_mismatch`, `span_mismatch`, and `score_mismatch` on `adeu_projection_alignment@0.1`.
2. Introduce deterministic diffing logic for bounding boxes / spans to capture structural "drift" vs "misses".
3. Keep diagnostics purely non-gating and evidence-oriented.

### Locks

- Evidence-only lock: Alignment diagnostics are purely informational and do not mutate projected semantics.
- Deterministic text/span comparison rules are frozen:
  - spans must be explicitly normalized/sorted before pairwise comparison.

### Acceptance

- Locked fixtures specifically targeting fuzzy boundaries (e.g. whitespace changes) successfully surface predictable mismatch diagnostics.
- `adeu_projection_alignment_determinism_pct == 100.0` maintains stability under the new checks.

## Path 11a: Normative Resolution Integrity (v16 Follow-on)

### Goal

Deepen formal integrity capabilities by introducing resolution strategies and full deontic coverage.

### Scope

1. Expand D3 deontic conflict checks to evaluate `permitted` vs `forbidden` interaction.
2. Implement deterministic conflict suppression logic using existing `excepts` edge types in the `adeu_core_ir@0.1`.
3. Expand D2 (cycle policy) beyond the `E` layer to include `D` layer dependency cycles.

### Locks

- Conflict suppression lock: `excepts` edge paths suppress D3 conflict emissions deterministically, but do *not* automatically alter canonical semantic outputs yet.
- Scope continuity: Only preexisting core-ir edge types are processed; no solver semantics update.

### Acceptance

- Deontic diagnostics predictably mask/suppress conflicts when valid `excepts` logic is supplied in fixtures.
- D2 cleanly detects and reports `self_cycle` permutations inside normative rule dependencies without blowing up path traversals.

## Path 12a: Solver Semantics Expansion (v4 Prep)

### Goal

Capitalize on the finalized reporting and integrity layers to introduce the first true multi-domain semantic expansion.

### Scope

1. Draft and freeze `docs/SEMANTICS_v4.md`.
2. Introduce Soft Constraint/Optimization capabilities into the `adeu.ir.v0` schema natively.
3. Map these soft constraints into `adeu_core_ir` deterministically.

### Locks

- Explicit versioning boundary: URM and semantic processors must cleanly parse the v4 syntax without breaking v3 legacy support.
- Trust projection update: Map objective priorities into existing metric definitions without disturbing exact deontic conflict policies.

### Acceptance

- Backwards compatibility guaranteed: All prior locked fixtures process equivalently.
- Stop-gate coverage explicitly accounts for v4 specific multi-lane interactions.

## Path 8b: Provider Maintenance (Fallback)

### Goal

Reserve a constrained fallback slice if provider parity regressions appear during v17 execution.

### Scope

1. fixture/matrix drift remediation only
2. no expansion of proposer surface set
3. additive tests + stop-gate evidence only

### Acceptance

- parity closeout metrics return to frozen thresholds without broad scope expansion.

## Decision Matrix

### If priority is completing diagnostic fidelity for projection extraction (v15 closure)

- Start with Path 10a.

### If priority is operationalizing deontic rules engines safely (v16 closure)

- Start with Path 11a.

### If priority is adding new reasoning capability (Optimization / Soft Constraints)

- Start with Path 12a.

### If provider parity regresses during v17 planning or execution

- invoke Path 8b fallback and defer broader expansion.

## Recommended Arc Order (v17+)

1. `vNext+17`: Path 11a — Normative Resolution Integrity (closes out formal D-layer logic on stable v16 base).
2. `vNext+18`: Path 10a — Extraction Fidelity Diagnostics (can run parallel or sequential without structural risk).
3. `vNext+19`: Path 12a — Solver Semantics Expansion (v4).

Why this order:

- Having fully resolved deontic logic (via `excepts` edges and `permitted` conditions) completes the formal integrity contract.
- Fine-grained extraction limits (spans/labels) from 10a are valuable, but non-blocking for solver correctness.
- Path 12a is the heaviest shift and benefits from 11a guaranteeing normative conflict bounds.

Fallback sequencing rule:

- if provider parity metrics regress below threshold during `vNext+17`, hold expansion and run Path 8b maintenance first.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` with Path 11a thin slice only:

1. `E1` deterministic deontic conflict expansion for `permitted` overlaps.
2. `E2` `excepts`-edge conflict suppression diagnostics.
3. `E3` D-layer cycle traversal policy checks.
4. `E4` manifest-driven coverage accounting + additive stop-gate metrics for `vNext+17 -> vNext+18`.

Suggested measured outcomes for `vNext+17 -> vNext+18` gate:

- `artifact_dangling_reference_determinism_pct == 100.0`
- `artifact_cycle_policy_determinism_pct == 100.0`
- `artifact_deontic_conflict_determinism_pct == 100.0`
- new `artifact_conflict_suppression_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression.
- all existing stop-gate tracked `vNext+6` through `vNext+16` metrics remain at threshold.
- previously collected closeout evidence remains green and reproducible.
