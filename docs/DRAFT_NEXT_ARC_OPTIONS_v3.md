# Draft Next Arc Options v3 (Post vNext+14 Planning)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS14.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft only (not frozen).
Goal: define post-`vNext+14` options and identify the concrete first slice for `vNext+15`.

## Consolidation Note

For post-`vNext+14` planning, this file remains the working source of truth.
`docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` remains historical context only.

## Baseline Snapshot (Post vNext+14)

Current baseline includes:

- `vNext+14` (`B1`-`B4`) complete and merged on `main`:
  - provider contract parity matrix + deterministic fail-closed route checks
  - codex candidate parse/shape normalization parity across ADEU/Concepts/Puzzles proposer modules
  - deterministic coverage accountability manifest + provider parity transfer report
  - additive stop-gate metrics for provider parity closeout
- v14 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `provider_route_contract_parity_pct=100.0`
  - `codex_candidate_contract_valid_pct=100.0`
  - `provider_parity_replay_determinism_pct=100.0`
- provider parity transfer report is stable and valid:
  - `schema=provider_parity_transfer_report.vnext_plus14@1`
  - `coverage_summary.valid=true`, `coverage_pct=100.0`
  - `parity_summary.valid=true`, `mapping_mismatch_count=0`
- prior arc guarantees remain green:
  - all stop-gate tracked `vNext+6` through `vNext+13` metrics remain at threshold
  - `vNext+12` and `vNext+13` closeout evidence remain reproducible

Net: provider reliability/parity hardening is complete enough to shift focus back to additive core-ir depth/reporting without changing solver semantics.

## Repo-Grounded Clarifications

1. Provider parity surface contracts are now frozen and fixture-backed for `vNext+14` scope:
   - `adeu.propose`
   - `concepts.propose`
   - `puzzles.propose`
   - `concepts.tournament.live_generation`
   - `concepts.tournament.replay_candidates`
2. `adeu_core_ir@0.1` remains additive and projection-first:
   - authoritative upstream semantics remain on `adeu.ir.v0` and `adeu.concepts.v0`.
3. Determinism boundary remains unchanged:
   - provider generation may be nondeterministic,
   - deterministic acceptance claims are enforced on persisted fixtures + deterministic transforms.
4. Next arc should avoid provider-surface churn and target core-ir depth/reporting only.

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

## Path 7b: Core-IR Depth + Lane Reporting (Recommended for vNext+15)

### Goal

Expand core-ir depth/reporting coverage on top of the stabilized provider parity base.

### Scope

1. Add deterministic lane reporting artifact(s) derived from frozen `adeu_core_ir@0.1` inputs.
2. Add deterministic projection/extraction alignment diagnostics as additive evidence (no semantic rewrites).
3. Add deterministic fixture coverage accounting and transfer-report evidence for the new depth surfaces.
4. Close out with additive `vNext+15` stop-gate metrics.

### Locks

- projection authority lock:
  - projected semantics remain authoritative when projection/extraction differ.
- diagnostics-only lock:
  - alignment outputs are evidence artifacts only and may not mutate canonical projected semantics.
- core-ir continuity lock:
  - `adeu_core_ir@0.1` and `adeu.sbr.v0_1` remain frozen unless explicit additive follow-on versioning is approved.
- replay lock:
  - deterministic acceptance/replay uses persisted fixtures only.

### Acceptance

- lane reporting artifacts are deterministic and replay-stable on locked fixtures.
- projection/extraction alignment diagnostics are deterministic and schema-valid.
- additive v15 stop-gate metrics pass at frozen thresholds.

### Risk

- depth/reporting fixture count can grow quickly; keep fixture inventory thin and coverage-justified.

## Path 9a: Formal Integrity Checks (Deferred)

### Goal

Add deterministic integrity checks over interconnected layer artifacts after depth/reporting stabilization.

### Scope

1. dangling reference checks
2. dependency cycle policy checks
3. minimal deontic conflict checks under shared conditions

### Locks

- integrity-only scope in first slice; no solver-semantics expansion.
- deterministic fail-closed reason-code ordering.

### Acceptance

- locked fixtures produce stable deterministic pass/fail artifacts.

## Path 8b: Provider Maintenance (Fallback)

### Goal

Reserve a constrained fallback slice if provider parity regressions appear during v15 execution.

### Scope

1. fixture/matrix drift remediation only
2. no expansion of proposer surface set
3. additive tests + stop-gate evidence only

### Acceptance

- parity closeout metrics return to frozen thresholds without broad scope expansion.

## Decision Matrix

### If priority is additive core-ir depth/reporting value on stable provider infrastructure

- Start with Path 7b.

### If priority is formal graph integrity enforcement

- Start Path 9a only after Path 7b closeout.

### If provider parity regresses during v15 planning or execution

- invoke Path 8b fallback and defer broader expansion.

## Recommended Arc Order (v15+)

1. `vNext+15`: Path 7 thin slice (`7b`) — core-ir depth + lane reporting + deterministic closeout
2. `vNext+16`: Path 9 thin slice (`9a`) — formal integrity checks
3. `vNext+17`: Path 8 maintenance (`8b`) only if provider parity regression requires targeted remediation

Why this order:

- provider reliability is now stabilized and should be exploited for depth/reporting value,
- it keeps deterministic closeout discipline consistent across arcs,
- it defers heavier formal integrity expansion until depth artifacts are operationally mature.

Fallback sequencing rule:

- if provider parity metrics regress below threshold during `vNext+15`, hold depth expansion and run Path 8b maintenance first.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md` with Path 7 follow-on thin slice (`7b`) only:

1. `C1` deterministic lane reporting contract and replay guarantees
2. `C2` deterministic projection/extraction alignment diagnostics (evidence-only)
3. `C3` manifest-driven coverage accountability + transfer-report refresh
4. `C4` additive stop-gate metrics for `vNext+15 -> vNext+16` closeout

Suggested measured outcomes for `vNext+15 -> vNext+16` gate:

- `adeu_lane_report_replay_determinism_pct == 100.0`
- `adeu_projection_alignment_determinism_pct == 100.0`
- `adeu_depth_report_replay_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression
- all existing stop-gate tracked `vNext+6` through `vNext+14` metrics remain at threshold
- `vNext+12`, `vNext+13`, and `vNext+14` closeout evidence remains green and reproducible
