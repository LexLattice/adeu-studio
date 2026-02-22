# Draft Next Arc Options v4 (Post vNext+16 Planning)

This document is the continuation-planning draft after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS16.md`
- `docs/INTEGRITY_TRANSFER_REPORT_vNEXT_PLUS16.md`
- `docs/SEMANTICS_v3.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`

Status: draft only (not frozen).
Goal: define post-`vNext+16` options and identify the concrete first slice for `vNext+17`.

## Consolidation Note

For post-`vNext+16` planning, this file is the working source of truth.
`docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` remains historical planning context only.

## Baseline Snapshot (Post vNext+16)

Current baseline includes:

- `vNext+16` (`D1`-`D4`) complete and merged on `main`:
  - deterministic dangling-reference diagnostics (`adeu_integrity_dangling_reference@0.1`)
  - deterministic dependency-cycle policy diagnostics (`adeu_integrity_cycle_policy@0.1`)
  - deterministic minimal deontic conflict diagnostics (`adeu_integrity_deontic_conflict@0.1`)
  - deterministic v16 manifest-driven coverage + transfer report + stop-gate closeout metrics
- v16 closeout is green:
  - `valid=true`
  - `all_passed=true`
  - `artifact_dangling_reference_determinism_pct=100.0`
  - `artifact_cycle_policy_determinism_pct=100.0`
  - `artifact_deontic_conflict_determinism_pct=100.0`
- integrity transfer report is stable and valid:
  - `schema=integrity_transfer_report.vnext_plus16@1`
  - `coverage_summary.valid=true`, `coverage_pct=100.0`
  - `replay_summary.valid=true`, `replay_count=3`
- prior arc guarantees remain green:
  - all stop-gate tracked `vNext+6` through `vNext+15` metrics remain at threshold
  - `vNext+12` through `vNext+15` closeout evidence remains reproducible

Net: the first integrity thin slice is complete and stable; next planning should choose between integrity-semantic expansion and targeted operational consolidation.

## Repo-Grounded Clarifications

1. Integrity diagnostics are currently evidence-first and non-authoritative.
   - no solver-semantics mutation is permitted by the `vNext+16` lock.
2. D1 scope is intentionally narrow today.
   - structural missing node/endpoint checks are in scope; artifact-reference integrity was deferred.
3. D2 scope is intentionally narrow today.
   - cycle checks are constrained to `E`-layer `depends_on` edges.
4. D3 scope is intentionally minimal today.
   - only `{obligatory, forbidden}` direct conflicts are included.
   - `permitted` modality interaction and `excepts`/`priority` suppression are deferred.
5. Stop-gate breadth is now substantial.
   - current closeout output includes `55` metrics and `36` gate booleans (`artifacts/stop_gate/metrics_v16_closeout.json`).
6. There is known duplicated validation logic in v16 reporting/metrics paths.
   - tracked in `docs/FUTURE_CLEANUPS.md` for possible shared-module extraction.

## Shared Locks For Any Next Arc

- No solver semantic contract changes unless explicitly versioned and locked.
- `docs/SEMANTICS_v3.md` remains authoritative unless a versioned follow-on lock says otherwise.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New behavior is additive-only unless explicitly marked breaking.
- Replay determinism is mandatory for acceptance paths.
- Runtime behavior must emit evidence events in `urm-events@1`.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- Deterministic claims must be grounded to persisted artifacts/hashes only.
- Stop-gate schema continuity remains additive on `stop_gate_metrics@1` unless explicitly re-locked.

## Path 9b: Integrity Semantics Expansion (Recommended for vNext+17)

### Goal

Expand integrity diagnostics beyond the minimal v16 surface while preserving evidence-first, deterministic behavior.

### Scope

1. Extend reference-integrity checks beyond node/edge endpoint structure.
2. Extend cycle policy coverage to include additional integrity-relevant graph surfaces (for example D-lane policy/exception cycles) with explicit deterministic boundaries.
3. Expand deontic conflict diagnostics to include deferred conflict cases (`permitted` interactions and deterministic `excepts`/`priority` evidence handling).
4. Additive fixture coverage accounting, transfer-report evidence updates, and stop-gate closeout metrics.

### Locks

- Integrity diagnostics remain evidence artifacts only (non-authoritative).
- Existing v16 schemas/metrics remain accepted and unchanged; any expansion is additive.
- Deterministic issue/conflict ordering, identity semantics, and replay hashing are frozen before implementation.
- Expanded diagnostics remain fail-closed on malformed fixtures and candidate-volume caps.

### Acceptance

- Locked expansion fixtures produce schema-valid deterministic outputs with replay-stable hashes.
- New additive v17 stop-gate metrics pass frozen thresholds.
- All existing tracked metrics remain at threshold.

### Risk

- Expansion of diagnostic taxonomies can drift without tight identity/normalization locks.

## Path 10a: Integrity Tooling Consolidation + CI Budget Hardening

### Goal

Reduce maintenance drift and CI/runtime pressure before further integrity semantic expansion.

### Scope

1. Extract shared v16 manifest/artifact validation logic into runtime-owned helper modules.
2. Add deterministic stop-gate runtime/budget visibility for regression detection.
3. Evaluate integrity schema-family consolidation strategy (`3 schemas` vs unified discriminator family) without breaking current contracts.
4. Normalize deterministic runtime-entrypoint environment enforcement (`TZ=UTC`, `LC_ALL=C`) through shared helpers.

### Acceptance

- Refactors are behavior-preserving and deterministic hashes remain unchanged on locked fixtures.
- CI/runtime budget reporting is reproducible and actionable.
- No gate or schema regressions are introduced.

### Risk

- Low feature visibility; high maintainability payoff.

## Path 8b: Provider Maintenance (Fallback)

### Goal

Reserve a constrained fallback slice if provider parity regressions appear during v17 planning or execution.

### Scope

1. fixture/matrix drift remediation only
2. no expansion of proposer surface set
3. additive tests + stop-gate evidence only

### Acceptance

- parity closeout metrics return to frozen thresholds without broad scope expansion.

## Decision Matrix

### If priority is deeper formal integrity coverage on the stabilized v16 base

- Start with Path 9b.

### If priority is reducing operational drift and CI budget risk first

- Start with Path 10a.

### If provider parity regresses during v17 planning/execution

- invoke Path 8b fallback and defer broader expansion.

## Recommended Arc Order (v17+)

1. `vNext+17`: Path 9 follow-on thin slice (`9b`) — integrity semantics expansion + deterministic closeout
2. `vNext+18`: Path 10 consolidation (`10a`) — shared validation/runtime budget hardening

Why this order:

- v16 established a stable deterministic integrity foundation and explicit deferred edges worth formalizing next,
- keeps integrity momentum while contracts are fresh and recently validated,
- retains a clear fallback to provider maintenance if parity regresses.

Fallback sequencing rule:

- if provider parity metrics regress below threshold during `vNext+17`, hold integrity expansion and run Path 8b maintenance first.

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS17.md` with Path 9 follow-on thin slice (`9b`) only:

1. `E1` deterministic extended reference-integrity diagnostics
2. `E2` deterministic extended cycle-policy diagnostics
3. `E3` deterministic deontic conflict-rule expansion (still evidence-first)
4. `E4` manifest-driven coverage accountability + additive stop-gate metrics for `vNext+17 -> vNext+18`

Suggested measured outcomes for `vNext+17 -> vNext+18` gate:

- `artifact_reference_integrity_determinism_pct == 100.0`
- `artifact_cycle_policy_extended_determinism_pct == 100.0`
- `artifact_deontic_conflict_expanded_determinism_pct == 100.0`
- no solver-semantics delta and no trust-lane regression
- all existing stop-gate tracked `vNext+6` through `vNext+16` metrics remain at threshold
- `vNext+12` through `vNext+16` closeout evidence remains green and reproducible
