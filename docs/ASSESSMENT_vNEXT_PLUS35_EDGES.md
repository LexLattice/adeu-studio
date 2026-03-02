# Assessment vNext+35 Edges (I1 Closure)

This document records `I1` closure status for v35 (`V31-F` + `V31-G` boundary-preparation arc) and isolates remaining `I2` implementation work.

Status: `I1` contract closure implemented (docs-only, no runtime behavior changes); `I2` implementation pending.

## Scope

- In scope: deterministic L2 boundary-release precondition contract closure and guard design readiness.
- Out of scope: runtime boundary release for `V31-F`/`V31-G`.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS34.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md`

## I1 Closure Checks (Completed)

1. Boundary candidate surfaces are frozen and addressable in contract text.
   - `V31-F` candidate surfaces:
     - `apps/api/src/adeu_api/urm_routes.py#urm_worker_run_endpoint`
     - `apps/api/src/adeu_api/urm_routes.py#urm_worker_cancel_endpoint`
     - `packages/urm_runtime/src/urm_runtime/capability_policy.py#authorize_action`
   - `V31-G` candidate surfaces:
     - `apps/api/src/adeu_api/main.py#_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`
     - `apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint`
     - `apps/api/src/adeu_api/storage.py#transaction`

2. Boundary readiness assertion contract is machine-checkable and target-separated.
   - exactly two `l2_boundary_readiness_assertion@1` blocks are present (`V31-F`, `V31-G`),
   - required keyset, ordering, enum, and uniqueness constraints are frozen,
   - `V31-F`/`V31-G` assertions remain independent (no merged block).

3. Release blocker authority is machine-mapped and deterministic.
   - authoritative blocker set is frozen in `l2_boundary_blocker_registry@1`,
   - readiness blocks reference blocker IDs from that registry only.

4. Source-of-truth and rollback preconditions are frozen.
   - `V31-F` source-of-truth: `capability_policy_authority`,
   - `V31-G` source-of-truth: `persisted_store_only`,
   - dual-read/dual-write remains forbidden unless explicitly authorized by a future lock update.

5. No-scaffolding and no-touch constraints are frozen in lock text.
   - no runtime release behavior is allowed in v35,
   - frozen no-touch runtime file list is explicitly defined for subsequent guard enforcement.

## Repository Baseline Confirmations

1. Worker endpoints remain ungated by `authorize_action`.
   - `urm_worker_run_endpoint` and `urm_worker_cancel_endpoint` are not policy-gated in baseline.

2. Proposer idempotency remains process-local.
   - `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` remains in-memory authority in baseline.

## Decisions Recorded

1. v36 release priority remains `V31-F` first; `V31-G` remains follow-on by default.
2. v35 boundary lock authority remains centralized in `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md` (no standalone parallel lock artifact in this arc).
3. Future release locks must include explicit rollback guarantees:
   - `V31-F`: deterministic denial payload contract plus all-or-nothing route-gate rollback semantics.
   - `V31-G`: single-source rollback semantics plus explicit migration-down contract requirement before release.

## Residual Risks Carried Into I2

1. Docs-contract drift risk remains until boundary lint is implemented and CI-enforced.
2. Accidental early release risk remains until no-touch diff and callgraph guards are executable.
3. Sentinel drift risk remains until baseline fixtures and normalization checks are implemented.

## I2 Implementation Readiness Checks (Planned)

1. Implement and gate `apps/api/scripts/lint_l2_boundary_readiness.py` with frozen CLI + exit-code contract.
2. Add no-touch merge-base diff guard enforcement for frozen runtime files.
3. Add worker run/cancel no-authorize-action callgraph guard.
4. Add behavior sentinel fixtures and deterministic normalization checks.
5. Keep closeout continuity lint green alongside new boundary lint.
