# Locked Continuation vNext+9 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS8.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- vNext+8 (`E1`-`E4`) merged on `main` with green CI and stop-gate `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` recommends `vNext+9 = Path 4` (runtime scale + recovery).
- This arc is reserved for runtime scale/recovery hardening only:
  - deterministic scheduler/concurrency contract first
  - restart recovery and cancellation/termination hardening second
  - stop-gate/runtime maintainability closeout third

## Global Locks

- No solver semantic contract changes in this arc.
- `docs/SEMANTICS_v3.md` remains authoritative and unchanged unless an explicit versioned follow-on lock is approved (none in this arc).
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`, `docs/LOCKED_CONTINUATION_vNEXT_PLUS7.md`, and `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md` remain authoritative for policy/proof/explain semantics.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Determinism boundary (runtime concurrency) is frozen:
  - deterministic normalization/materialization/replay is guaranteed for identical persisted scheduler/worker records (including dispatch tokens and worker lifecycle events).
  - live concurrent execution ordering is not claimed; replay determinism is grounded to persisted dispatch tokens and event streams.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Worker lifecycle taxonomy lock remains frozen:
  - worker lifecycle events remain `WORKER_START`, `WORKER_CANCEL`, `WORKER_FAIL`, `WORKER_PASS`.
  - concurrency/recovery distinctions must be encoded in deterministic detail fields (for example `dispatch_seq`, `lease_id`, `phase`, `reason`) rather than introducing near-duplicate event names.
- Worker lifecycle detail minimum lock is frozen:
  - all dispatched-child `WORKER_*` events must include:
    - `dispatch_seq`
    - `lease_id`
    - `parent_stream_id`
    - `parent_seq`
    - `child_id`
    - `phase_at_event`
  - `WORKER_FAIL` must include deterministic `reason` and `code`.
  - when cancel lineage exists, `cancel_request_id` is required on `WORKER_CANCEL` and any cancel-caused terminal event.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- Hidden randomness is forbidden in deterministic/replay mode:
  - UUID/random ids must be either explicitly provided as input, derived from canonical deterministic hashes, or used only behind the persisted-artifact determinism boundary.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Runtime scheduling/recovery decisions and reports must be reproducible from persisted artifacts only:
  - no live environment/process reads for deterministic replay decisions.
- Scheduler token persistence model is frozen:
  - dispatch tokens are persisted in a dedicated SQL surface (`urm_dispatch_token`) with deterministic constraints.
  - `scheduler_dispatch_token@1` is a validation/reporting projection of SQL token rows; it may be materialized for evidence export but is not source-of-truth persistence.
- Versioned artifacts introduced in this arc must have explicit schemas under `spec/`:
  - `scheduler_dispatch_token@1` (validation/reporting projection schema)
- Recovery startup ordering lock is frozen:
  - stale-run recovery must complete before new spawn/dispatch requests are accepted for the process.
- Stop-gate metrics remain additive on `stop_gate_metrics@1`:
  - no schema-family fork unless an explicit later lock approves it.
- Canonical serialization profile is frozen for deterministic artifacts in this arc:
  - UTF-8 JSON
  - object keys sorted lexicographically
  - deterministic list ordering per each artifact lock
  - absent fields omitted (no implicit null insertion)

## Arc Scope (Draft Lock)

This arc proposes only Path 4 thin-slice implementation:

1. `R1` Scheduler token persistence + controlled concurrency rollout
2. `R2` Restart recovery + orphan lease deterministic handling
3. `R3` Concurrent cancellation/termination + budget-accounting determinism
4. `R4` Runtime decomposition + replay metrics/stop-gate hardening

## R1) Scheduler Token + Concurrency Thin Slice

### Goal

Increase orchestration throughput with deterministic scheduler semantics.

### Scope

- Controlled increase to concurrent child execution:
  - `max_active_children = 2` for thin slice (no higher in this arc).
- Persist deterministic scheduler token per dispatch decision.
- Freeze lease semantics for thin slice:
  - `lease_id := worker_run_id`.
- Preserve deterministic queue ordering and replay behavior.
- Freeze scheduler phase model for thin slice:
  - `queued -> leased -> started -> terminal` (monotonic, no backward transition).

### Locks

- Concurrency cap lock is frozen:
  - this arc may raise active concurrency to `2` only.
- Lease semantics lock is frozen:
  - `lease_id` is an alias of persisted `worker_run_id` in this arc.
- Scheduler token contract is frozen:
  - token must include:
    - `parent_stream_id`
    - `parent_seq`
    - `parent_session_id`
    - `queue_seq`
    - `dispatch_seq` (monotonic)
    - `child_id`
    - `worker_run_id` (`lease_id`)
    - dispatch `phase`
- Token uniqueness lock is frozen:
  - `(parent_session_id, dispatch_seq)` is unique.
  - duplicate dispatch token rows fail closed with `URM_SCHEDULER_REPLAY_ORDER_INVALID`.
- Queue sequence uniqueness lock is frozen:
  - `(parent_session_id, queue_seq)` is unique.
- Worker run id uniqueness lock is frozen:
  - `(parent_session_id, worker_run_id)` is unique.
- Collision handling lock is frozen:
  - duplicate key insertion on queue/lease anchor fields fails closed with `URM_DISPATCH_LEASE_CONFLICT`.
- Dispatch sequence allocation lock is frozen:
  - `dispatch_seq` allocation is serialized per `parent_session_id` using one deterministic SQL transaction (`MAX(dispatch_seq) + 1` under parent-scoped lock).
  - concurrent workers may not allocate `dispatch_seq` for the same parent in parallel outside the serialized transaction boundary.
- Dispatch sequence contiguity lock is frozen:
  - `dispatch_seq` must be strictly monotonic but need not be contiguous; gaps are permitted and non-semantic.
- Replay ordering lock is frozen:
  - replay resolves dispatch order from persisted `dispatch_seq`; replay may not recompute scheduling decisions.
- Queue key ordering lock is frozen:
  - scheduler/recovery may not reorder persisted queue keys.
- Queue/order anchor persistence lock is frozen:
  - `queue_seq` and `dispatch_seq` must be persisted at spawn/dispatch time.
  - restart recovery must seed next sequence values from persisted maxima (`max + 1`) per parent scope; it may not restart from empty in-memory counters.
- Parent-stream interleaving lock is frozen:
  - parent-visible worker lifecycle records under concurrency must include deterministic ordering anchors (`dispatch_seq`, `lease_id`).
- Deterministic ID-generation lock is frozen:
  - in deterministic/replay mode, `worker_run_id` (`lease_id`) must be explicit input or deterministic derivation from persisted scheduler anchors (for example canonical hash over `parent_session_id + dispatch_seq`).
  - live mode may use random IDs, but replay determinism is grounded to the persisted IDs.
- Phase/event atomicity lock is frozen:
  - transition to `started` must be persisted in the same transaction that appends corresponding `WORKER_START`.
  - transition to `terminal` must be persisted in the same transaction that appends corresponding terminal `WORKER_PASS|WORKER_FAIL|WORKER_CANCEL`.
  - non-atomic phase/event transition detection fails closed with `URM_SCHEDULER_PHASE_EVENT_ATOMICITY_VIOLATION`.
- Scheduler order/lease conflict code locks are frozen:
  - `URM_SCHEDULER_REPLAY_ORDER_INVALID`
  - `URM_DISPATCH_LEASE_CONFLICT`

### Acceptance

- Identical persisted queue/scheduler state replays to byte-identical dispatch ordering.
- Concurrency fixture with `max_active_children = 2` replays deterministically across reruns.

## R2) Restart Recovery + Orphan Lease Rule

### Goal

Harden restart recovery under concurrency without replay drift.

### Scope

- Freeze deterministic recovery behavior for leased-but-not-started dispatches.
- Ensure restart recovery emits deterministic failure evidence and linkage.

### Locks

- Restart recovery split-path lock is frozen:
  - started dispatches and non-started dispatches are handled by distinct deterministic rules.
- Started-child restart behavior lock is frozen:
  - if start is observed for the dispatch token, restart path remains existing deterministic behavior:
    - emit `WORKER_FAIL` with `URM_CHILD_TERMINATED_ON_RESTART`.
- Orphan lease recovery rule is frozen:
  - on restart, any dispatch token with no observed start emits deterministic `WORKER_FAIL` with reason `lease_orphaned`.
- Orphan lease failure code lock is frozen:
  - `URM_SCHEDULER_LEASE_ORPHANED`
- Start-detection lock is frozen:
  - start is considered observed if and only if persisted scheduler token `phase in {started, terminal}`.
  - worker-run status values alone are non-authoritative for start detection in this arc.
- Recovery ordering lock is frozen:
  - restart recovery processing order is deterministic by persisted `dispatch_seq`.
- Recovery processing mode lock is frozen:
  - orphan/started restart recovery is processed sequentially per parent in `dispatch_seq` order.
- Event placement/linkage lock is frozen:
  - orphan recovery appends to child stream and includes deterministic linkage fields (`parent_stream_id`, `parent_seq`, `dispatch_seq`, `lease_id`).
- Recovery behavior lock is frozen:
  - orphaned leases are terminalized; recovery may not silently re-dispatch them in this arc.
- Crash-tolerant event append lock is frozen:
  - if a target NDJSON event stream has a trailing partial line after crash, recovery must deterministically repair/truncate the trailing partial fragment before appending restart failure events.

### Acceptance

- Restart recovery fixtures replay byte-identically across reruns.
- Orphan lease fixtures emit frozen event/code/reason deterministically.

## R3) Concurrency Cancel/Terminate + Budget Determinism

### Goal

Keep cancellation/termination and budget behavior deterministic under concurrent children.

### Scope

- Freeze one explicit concurrent budget accounting model.
- Harden deterministic cancellation/termination propagation with interleaving constraints.

### Locks

- Budget accounting model lock is frozen:
  - model selected for this arc is `running_total_v1` (shared parent budget lane with persisted running totals).
- Mixed accounting lock is frozen:
  - mixed `reservation` + `running-total` behavior is forbidden.
- Budget running-total persistence surface lock is frozen:
  - running totals are persisted in a dedicated deterministic budget record keyed by `(parent_session_id, budget_lane)`.
- Budget lane enum lock is frozen:
  - `budget_lane in {solver_calls, duration_secs, tokens}`.
- Budget authority lock is frozen:
  - persisted parent running totals are authoritative for enforcement.
  - child `budget.v1` snapshots are deterministic projection inputs and may not override authoritative parent totals.
- Atomic budget update lock is frozen:
  - running-total check + increment must execute in one serialized transaction per `(parent_session_id, budget_lane)`.
  - concurrent contenders are resolved by commit order in that transaction boundary; first committed debit is accepted, later debit beyond threshold fails deterministically with `URM_CHILD_BUDGET_EXCEEDED`.
- Budget accounting mode code lock is frozen:
  - `URM_DISPATCH_ACCOUNTING_MODE_INVALID`
- Budget breach behavior remains frozen and deterministic:
  - `URM_CHILD_BUDGET_EXCEEDED` remains authoritative for breach terminalization.
- Cancel-already-terminal lock is frozen:
  - if child is already terminal when cancel is processed, cancel resolves deterministically as `already_terminal` and does not emit `WORKER_CANCEL`.
- Cancel lineage lock is frozen:
  - cancel requests carry `cancel_request_id` (idempotency key or deterministic derived key).
  - any emitted `WORKER_CANCEL` and any terminal event caused by that cancel must include the same `cancel_request_id`.
- Cancel/terminate propagation lock is frozen:
  - for a given child, `WORKER_CANCEL` (if emitted) must precede any terminal worker event with later `parent_seq` for the same cancel request lineage.
- Cancel ordering scope lock is frozen:
  - ordering guarantees in this arc are per-child lineage only; no global total ordering of cancel/terminal events across different children is claimed in live mode.
- Interleaving replay lock is frozen:
  - parent-visible interleaving under concurrency is accepted only when sequence anchors (`seq`, `dispatch_seq`, `lease_id`) are replay-stable.
- Live-time boundary lock is frozen:
  - live cancel/timeout paths may use wall-clock timers (for example cancel wait windows), but replay acceptance is grounded to persisted terminal outcomes/evidence events, not live timer schedule equivalence.

### Acceptance

- Concurrent cancel/terminate fixtures replay byte-identically across reruns.
- Concurrent budget fixtures show deterministic code/event outcomes and stable counters.

## R4) Runtime Decomposition + Stop-Gate Hardening

### Goal

Reduce runtime maintenance risk while adding machine-checkable closeout gates for Path 4.

### Scope

- Decompose high-risk runtime orchestration logic touched by concurrency/recovery changes.
- Extend additive stop-gate metrics with vNext+9 runtime scale/recovery keys.

### Locks

- Decomposition prerequisite is frozen:
  - extract and isolate runtime scale/recovery logic into explicit modules:
    - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`:
      - `_spawn_child_v2`, dispatch token persistence, dispatch ordering enforcement
    - `packages/urm_runtime/src/urm_runtime/child_workflow.py`:
      - `_run_child_workflow_v2`
    - `packages/urm_runtime/src/urm_runtime/child_recovery.py`:
      - `_recover_stale_child_runs`, orphan-lease handling
    - `packages/urm_runtime/src/urm_runtime/child_budget.py`:
      - running-total accounting and deterministic budget checks under concurrency
- Behavior parity lock is frozen:
  - extracted modules must preserve pre/post behavior with deterministic parity fixtures.
  - no behavior changes are allowed from decomposition alone except those explicitly version-locked in `R1`-`R3`.
- Dispatch failure-path consolidation lock is frozen:
  - duplicated queued-child failure handling paths in scheduler dispatch flow must be extracted to one helper in `child_dispatch.py` (for example `_fail_queued_child_unlocked`).
  - consolidation is maintainability-only and must preserve identical event/code payload semantics.
- Recovery extraction-helper consolidation lock is frozen:
  - repeated token/metadata fallback extraction logic inside restart recovery must be extracted to one helper in `child_recovery.py`.
  - consolidation is maintainability-only and must preserve identical recovery classification, ordering anchors, and emitted payload fields.
- Shared-state extraction lock is frozen:
  - thread-run registry ownership remains in runtime coordinator state.
  - extracted modules must interact through an explicit injected runtime state interface; hidden module-level mutable thread state is forbidden.
- Additive metric keys are frozen on `stop_gate_metrics@1`:
  - `scheduler_dispatch_replay_determinism_pct`
  - `orphan_lease_recovery_determinism_pct`
  - `concurrent_budget_cancel_stability_pct`
- Determinism metric computation algorithm is frozen:
  - canonical hash per artifact/fixture
  - replay exactly `N=3` times per fixture
  - fixture passes only when all replay hashes match
  - `pct = 100 * passed / total`
- Metric denominator and fixture selection are frozen:
  - fixture selection is defined by a locked manifest file:
    - `apps/api/fixtures/stop_gate/vnext_plus9_manifest.json`
  - manifest schema is frozen:
    - `stop_gate.vnext_plus9_manifest@1`
  - `total` for each vNext+9 metric equals number of fixture entries listed for that metric in the manifest.
- Manifest-hash lock is frozen:
  - stop-gate output must include `vnext_plus9_manifest_hash`.
  - hash is computed as `sha256(canonical_json(manifest_payload))`.
  - metric computation is invalid if runtime manifest hash does not match recomputed canonical hash.
- Metrics are computed only from locked fixtures/replay artifacts.
- No live-run data may be mixed into deterministic stop-gate deltas.
- Concurrent fixture assertion model lock is frozen:
  - replay fixtures for persisted scheduler/recovery artifacts remain byte-identical.
  - live-concurrency parity fixtures use deterministic equivalence assertions:
    - set-equivalence of emitted lifecycle events,
    - per-child lineage ordering invariants,
    - stable terminal code/reason and budget-counter outcomes.
- `vNext+9 -> vNext+10` thresholds are frozen:
  - `scheduler_dispatch_replay_determinism_pct == 100.0`
  - `orphan_lease_recovery_determinism_pct == 100.0`
  - `concurrent_budget_cancel_stability_pct == 100.0`
  - if any fail: continue Path 4 hardening; do not start Path 5.

### Acceptance

- Stop-gate runtime metrics are reproducible across reruns for identical fixture inputs.
- Stop-gate report captures deterministic pass/fail for all frozen vNext+9 thresholds.
- Decomposition parity fixtures pass with no deterministic regression.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Runtime scale/recovery code families in this arc are explicit/additive:
  - `URM_SCHEDULER_*`
  - `URM_DISPATCH_*`
  - existing `URM_CHILD_*` for child budget/terminal behavior
- Frozen additions in this arc:
  - `URM_SCHEDULER_REPLAY_ORDER_INVALID`
  - `URM_SCHEDULER_LEASE_ORPHANED`
  - `URM_SCHEDULER_PHASE_EVENT_ATOMICITY_VIOLATION`
  - `URM_DISPATCH_LEASE_CONFLICT`
  - `URM_DISPATCH_ACCOUNTING_MODE_INVALID`
- Existing restart code reuse lock:
  - started-child restart path continues to use `URM_CHILD_TERMINATED_ON_RESTART`.
- Endpoint/code mapping remains explicit and additive-only.

## Commit Plan (Small Green Commits)

1. `runtime: extract dispatch/workflow/recovery/budget modules with parity fixtures (no behavior change)`
2. `runtime: add scheduler dispatch token SQL persistence + deterministic concurrency cap fixtures`
3. `runtime: harden restart split-path recovery (started vs. orphan lease) with deterministic event/code linkage`
4. `runtime: harden concurrent cancel/terminate + running-total budget accounting determinism`
5. `metrics: extend stop-gate with vnext+9 manifest-driven runtime determinism keys`

## Exit Criteria (Draft)

- `R1`-`R4` merged with green CI.
- Scheduler dispatch replay determinism is `100%` on locked fixtures.
- Orphan lease recovery determinism is `100%` on locked fixtures.
- Concurrent budget/cancel stability is `100%` on locked fixtures.
- `vNext+9 -> vNext+10` frozen stop-gate thresholds all pass.
- No solver semantics contract delta and no trust-lane regression introduced.
- All existing `vNext+6`, `vNext+7`, and `vNext+8` determinism metrics remain at threshold.
