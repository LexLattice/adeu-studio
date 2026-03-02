# Assessment vNext+35 Edges (I1 + I2 Implementation)

This document records v35 implementation status for `V31-F`/`V31-G` boundary-preparation, with `I1` contract closure and `I2` deterministic guard execution artifacts.

Status: `I1` + `I2` implemented on branch; pending merge and stop-gate closeout.

## Scope

- In scope: deterministic boundary-precondition contracts and anti-release guard enforcement.
- Out of scope: runtime boundary release for `V31-F`/`V31-G`.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS34.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS34.md`

## I1 Contract Closure (Implemented)

1. Boundary inventory for deferred release surfaces is frozen and target-separated (`V31-F`, `V31-G`).
2. `l2_boundary_readiness_assertion@1` lock grammar is machine-checkable with frozen keysets and ordering rules.
3. `l2_boundary_blocker_registry@1` authority and blocker membership linkage are frozen.
4. Single-source-of-truth and rollback preconditions are explicit for both deferred release paths.
5. No-scaffolding and no-touch runtime constraints are frozen in lock text.

## I2 Guard Suite (Implemented)

1. Boundary-readiness lint entrypoint is implemented:
   - `apps/api/scripts/lint_l2_boundary_readiness.py`
2. Frozen sentinel fixtures are implemented:
   - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_run_response_v34_baseline.json`
   - `apps/api/tests/fixtures/l2_boundary_sentinels/v35_worker_cancel_response_v34_baseline.json`
3. Deterministic lint/guard tests are implemented:
   - `apps/api/tests/test_l2_boundary_readiness_lint.py`
4. CI enforcement is wired:
   - `.github/workflows/ci.yml` runs frozen lint CLI with `TZ=UTC` and `LC_ALL=C`.

## Guard Contract Checks Covered by I2 Implementation

1. Readiness assertion checks:
   - exactly two readiness blocks required under `## L2 Boundary Readiness Assertions (Machine-Checkable)`,
   - target set must be exactly `V31-F` and `V31-G`,
   - keyset/enum/ordering validation is fail-closed.
2. Blocker registry checks:
   - exactly one `l2_boundary_blocker_registry@1` block required,
   - readiness `release_blockers` must resolve to registry IDs.
3. Merge-base diff guard checks:
   - no-touch runtime file modifications are merge-blocking,
   - base-ref unresolvable state fails closed with deterministic exit code `5`.
4. Callgraph and behavior checks:
   - no-authorize-action-calls guard for worker run/cancel paths is fail-closed,
   - sentinel behavior drift checks are deterministic and fail-closed.
5. Sentinel provenance/normalization checks:
   - fixture metadata contract is validated,
   - recursive high-entropy exclusion is enforced during response comparison.

## Repository Baseline Confirmations (Unchanged by v35)

1. Worker run/cancel endpoints remain ungated by `authorize_action`.
2. Proposer idempotency authority remains process-local (`_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`).
3. No runtime behavior implementation files from the frozen no-touch list are modified in v35 scope.

## Residual Risks to Close in Stop-Gate Phase

1. Final merge evidence still depends on green CI execution of new boundary lint step.
2. v35 closeout document still needs runtime-observability comparison row against v34 baseline.
3. No-release posture must remain explicit in closeout language (boundary prep only).

## Next Actions

1. Merge v35 `I2` implementation PR after green CI.
2. Draft `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS35.md` with required machine-checkable row against v34 baseline.
3. Re-baseline `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md` for v36 release-candidate sequencing after v35 closeout.
