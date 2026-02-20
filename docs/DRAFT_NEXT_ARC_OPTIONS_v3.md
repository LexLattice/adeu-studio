# Draft Next Arc Options v3 (Post vNext+15 Planning)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS15.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: planning draft completed for `vNext+16`; superseded for active planning after v16 closeout.
Goal: historical record of post-`vNext+15` optioning and the selected first slice for `vNext+16`.

Closeout note (February 20, 2026 UTC):

- Selected path `9a` was executed in `vNext+16` (`D1`-`D4`) and merged on `main`.
- Closeout decision evidence is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`.
- Active next-arc planning should move to `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md`.

## Consolidation Note

For post-`vNext+15` planning, this file served as the working source of truth during `vNext+16` selection.
After `vNext+16` closeout, it remains historical planning context.
`docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` remains historical context only.

## Baseline Snapshot (Post vNext+15)

Current baseline includes:

- `vNext+15` (`C1`-`C4`) complete and merged on `main`:
  - deterministic lane-report contract (`adeu_lane_report@0.1`) and validators
  - deterministic projection/extraction alignment diagnostics (`adeu_projection_alignment@0.1`, evidence-only)
  - deterministic depth-coverage manifest + transfer report
  - additive stop-gate metrics for depth closeout
- v15 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `adeu_lane_report_replay_determinism_pct=100.0`
  - `adeu_projection_alignment_determinism_pct=100.0`
  - `adeu_depth_report_replay_determinism_pct=100.0`
- core-ir depth transfer report is stable and valid:
  - `schema=core_ir_depth_transfer_report.vnext_plus15@1`
  - `coverage_summary.valid=true`, `coverage_pct=100.0`
  - `alignment_summary.valid=true`
  - `replay_summary.valid=true`, `replay_count=3`
- prior arc guarantees remain green:
  - all stop-gate tracked `vNext+6` through `vNext+14` metrics remain at threshold
  - `vNext+12`, `vNext+13`, and `vNext+14` closeout evidence remain reproducible

Net: additive core-ir depth/reporting hardening is complete enough to shift focus to formal integrity checks while preserving projection-first and solver-semantics stability.

## Repo-Grounded Clarifications

1. Core-ir reporting artifacts are now explicitly layered and additive:
   - `adeu_core_ir@0.1` (canonical core-ir)
   - `adeu_lane_projection@0.1` (projection structure)
   - `adeu_lane_report@0.1` (deterministic lane summary)
   - `adeu_projection_alignment@0.1` (deterministic evidence diagnostics)
2. Projection authority remains unchanged:
   - alignment diagnostics are evidence-only and may not mutate canonical projected semantics.
3. Determinism boundary remains unchanged:
   - deterministic acceptance claims are enforced on persisted fixtures + deterministic transforms.
4. Provider parity continuity remains unchanged:
   - provider matrix/manifest behavior frozen in `vNext+14` stays out-of-scope for expansion in the next arc.

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

## Path 9a: Formal Integrity Checks (Recommended for vNext+16)

### Goal

Add deterministic integrity checks over interconnected artifacts after depth/reporting stabilization.

### Scope

1. Deterministic dangling-reference checks across frozen artifact links.
2. Deterministic dependency-cycle policy checks.
3. Deterministic minimal deontic conflict checks under shared conditions.
4. Additive fixture coverage accounting, transfer-report evidence, and stop-gate closeout metrics.

### Locks

- integrity-check-only lock:
  - first slice enforces structural integrity diagnostics only; no solver-semantics expansion.
- fail-closed determinism lock:
  - deterministic issue classification, deterministic reason-code ordering, deterministic replay hashing.
- continuity lock:
  - projection-first authority and provider-parity freeze remain unchanged.

### Acceptance

- locked integrity fixtures produce schema-valid deterministic outputs with replay-stable hashes.
- additive v16 stop-gate metrics pass frozen thresholds.

### Risk

- multi-artifact fixture growth can expand quickly; keep inventory thin-slice and coverage-justified.

## Path 8b: Provider Maintenance (Fallback)

### Goal

Reserve a constrained fallback slice if provider parity regressions appear during v16 execution.

### Scope

1. fixture/matrix drift remediation only
2. no expansion of proposer surface set
3. additive tests + stop-gate evidence only

### Acceptance

- parity closeout metrics return to frozen thresholds without broad scope expansion.

## Decision Matrix

### If priority is formal artifact integrity enforcement on the stabilized v15 reporting base

- Start with Path 9a.

### If provider parity regresses during v16 planning or execution

- invoke Path 8b fallback and defer broader expansion.

## Recommended Arc Order (v16+)

1. `vNext+16`: Path 9 thin slice (`9a`) — formal integrity checks + deterministic closeout
2. `vNext+17`: Path 8 maintenance (`8b`) only if provider parity regression requires targeted remediation

Why this order:

- v15 depth/reporting outputs are now stable and provide a better substrate for integrity policies,
- it keeps deterministic closeout discipline consistent across arcs,
- it avoids mixing provider-surface maintenance into the first integrity slice unless a regression forces it.

Fallback sequencing rule:

- if provider parity metrics regress below threshold during `vNext+16`, hold integrity expansion and run Path 8b maintenance first.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md` with Path 9 thin slice (`9a`) only:

1. `D1` deterministic dangling-reference checks and fixed issue taxonomy
2. `D2` deterministic dependency-cycle policy checks
3. `D3` deterministic minimal deontic conflict checks (evidence-first)
4. `D4` manifest-driven coverage accountability + additive stop-gate metrics for `vNext+16 -> vNext+17`

Suggested measured outcomes for `vNext+16 -> vNext+17` gate:

- `artifact_dangling_reference_determinism_pct == 100.0`
- `artifact_cycle_policy_determinism_pct == 100.0`
- `artifact_deontic_conflict_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression
- all existing stop-gate tracked `vNext+6` through `vNext+15` metrics remain at threshold
- `vNext+12` through `vNext+15` closeout evidence remains green and reproducible
