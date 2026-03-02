# Assessment vNext+35 Edges (Draft)

This document tracks v35 (`V31-F` + `V31-G` boundary-preparation arc, `I1`-`I2`) edge assessment and freeze-readiness notes.

Status: draft working notes (not frozen).

## Scope

- In scope: deterministic L2 boundary-release precondition contract closure and guard rails.
- Out of scope: runtime boundary release for `V31-F`/`V31-G`.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS34.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md`

## Repository State Checks (Current)

1. All candidate boundary surfaces are present and addressable
   - `V31-F` candidate surfaces:
     - `apps/api/src/adeu_api/urm_routes.py#urm_worker_run_endpoint`
     - `apps/api/src/adeu_api/urm_routes.py#urm_worker_cancel_endpoint`
     - `packages/urm_runtime/src/urm_runtime/capability_policy.py#authorize_action`
   - `V31-G` candidate surfaces:
     - `apps/api/src/adeu_api/main.py#_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`
     - `apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint`
     - `apps/api/src/adeu_api/storage.py#transaction`

2. Worker endpoints remain ungated by `authorize_action`
   - `urm_worker_run_endpoint` and `urm_worker_cancel_endpoint` do not route through policy authorization in current baseline.
   - gap remains consistent with `V31-F` planning intent.

3. Proposer idempotency remains process-local
   - `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` is an in-memory authority in current baseline.
   - `urm_core_ir_propose_endpoint` reads/writes this map; restart loses idempotency state.

## Candidate Risk Register (Updated)

1. Boundary ambiguity risk (authorization release path)
   - risk: future implementation starts without frozen denial/rollback contract text.
   - mitigation target: target-specific machine-checkable readiness block for `V31-F`.

2. Boundary ambiguity risk (idempotency persistence release path)
   - risk: dual-source or partial migration semantics introduced without lock authority.
   - mitigation target: `persisted_store_only` source-of-truth requirement + explicit dual-read/dual-write prohibition unless later lock defines migration semantics.

3. Accidental early release risk
   - risk: policy/persistence boundary changes land under preparatory arc.
   - mitigation target: merge-blocking no-touch diff guard for frozen runtime files.

4. Docs-contract drift risk
   - risk: manual edits produce ambiguous or non-machine-checkable lock interpretation.
   - mitigation target: deterministic schema parsing of exactly two `l2_boundary_readiness_assertion@1` blocks.

5. Sentinel drift risk
   - risk: behavior snapshots become hand-authored or drift from v34 baseline.
   - mitigation target: frozen sentinel fixture paths + provenance lock to v34 merge baseline (`fd9a48de8ab7852d371080659c9fc15aa24b8b70`).

6. Diff-guard false-positive risk
   - risk: no-touch enforcement trips on upstream churn rather than branch-authored changes.
   - mitigation target: frozen merge-base (`origin/main...HEAD`) branch-owned diff semantics; raw two-dot diff forbidden.

## Guard Architecture Checks (v35)

1. Boundary readiness lint contract
   - entrypoint: `apps/api/scripts/lint_l2_boundary_readiness.py`
   - fixed CLI: includes `--lock-doc`, `--base-ref`, `--sentinel-dir`
   - fixed exit-code contract: `0` (pass), `2` (schema/placement), `3` (no-touch diff), `4` (sentinel drift), `5` (base-ref unavailable)
   - release blockers are machine-mapped through authoritative `l2_boundary_blocker_registry@1` (`DOC`/`CHECK` refs).

2. No-touch runtime-file guard
   - frozen files:
     - `apps/api/src/adeu_api/urm_routes.py`
     - `packages/urm_runtime/src/urm_runtime/capability_policy.py`
     - `apps/api/src/adeu_api/main.py`
     - `apps/api/src/adeu_api/storage.py`
   - diff semantics: merge-base/branch-owned (`origin/main...HEAD`), not raw two-dot.
   - callgraph complement: worker run/cancel path guard fails if `authorize_action` is invoked in v35.

3. Behavior sentinel guard
   - frozen fixture paths:
     - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_run_response_v34_baseline.json`
     - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_cancel_response_v34_baseline.json`
   - comparison authority: canonical JSON response payloads with recursive high-entropy field exclusion (`created_at`, `timestamp`, `generated_at`, `request_id`, `trace_id`, `hostname`, `pid`).
   - fixture metadata contract: top-level `meta` with `captured_from_commit`, `captured_by_script`, `captured_at`; `captured_from_commit` must match frozen v34 merge commit.

## Pre-Freeze Checks (Planned)

1. Validate exactly two readiness assertion blocks (`V31-F`, `V31-G`) exist with frozen schema/keyset/order rules.
2. Validate `l2_boundary_blocker_registry@1` exists and readiness blockers resolve to registry IDs.
3. Verify no-touch guard stays green for all v35 PR commits under merge-base semantics.
4. Verify worker run/cancel callgraph guard confirms no `authorize_action` invocation in v35.
5. Verify behavior sentinel snapshots (with metadata contract) match v34 baseline outputs under deterministic normalization.
6. Verify closeout continuity lint remains green after v35 docs/guards land.

## Open Questions

1. Keep v36 release target fixed to `V31-F` first (default), or leave reprioritizable until v35 freeze?
2. Do we want a dedicated standalone boundary lock artifact in v35, or keep lock authority solely in `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md`?
3. Which minimum rollback guarantees must be mandatory text in v36 (`V31-F`) and v37 (`V31-G`) release locks?
