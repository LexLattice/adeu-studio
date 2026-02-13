# Locked Continuation vNext+5 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS4.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS4.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v1.md` (Option B reference scope)

Status: draft lock (not frozen yet).

Decision basis:

- vNext+4 (`A1`-`A5`) merged on `main` with green CI.
- vNext+4 stop-gate draft currently recommends `GO_OPTION_B`.
- This arc is reserved for **Option B deepening only**.

## Assessment Integrations (GPT + Opus)

This draft incorporates the latest GPT + Opus review deltas before freeze:

- queue ordering key and cancel/dispatch ordering are explicitly frozen.
- `v1` -> `v2` queue-mode migration/default behavior is explicitly frozen.
- budget semantics now include measurement-source locks and deterministic breach behavior.
- connector discovery now distinguishes raw snapshot evidence vs filtered exposure mapping.
- replay/live boundary and stale-snapshot predicates are explicitly frozen.
- steer target alias resolution algorithm and denied-event symmetry are explicitly frozen.
- fixture requirements now include queue-cancel race and deterministic budget-breach replay.

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`, including deterministic failure paths.
- Event taxonomy alignment is frozen to existing `urm-events@1` families:
  - worker lifecycle events remain `WORKER_START`, `WORKER_CANCEL`, `WORKER_FAIL`, `WORKER_PASS`.
  - steer lifecycle events remain `STEER_APPLIED`, `STEER_DENIED`.
  - phase/state distinctions (for example `queued` vs `running`) must be encoded in deterministic detail fields (for example `detail.phase`) rather than introducing near-duplicate event names.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Policy/runtime governance outputs must be reproducible from persisted artifacts only:
  - no live environment/process state reads for deterministic decisions/reports.
- Dynamic-runtime execution mode must be explicit:
  - `execution_mode = live | replay`.
- In replay mode, all decisions must be resolved from persisted artifacts only.
- Versioned artifacts/registries introduced or formalized in this arc must have explicit schemas under `spec/`:
  - `connector_snapshot@1`
  - `connector_exposure_mapping.v1.json`
  - `budget.v1` (when persisted or validated outside transient in-memory runtime state)

## Arc Scope (Draft Lock)

This arc proposes only Option B deepening:

1. `B1` Controlled multi-child delegation with deterministic queueing
2. `B2` Parent-child budget inheritance and deterministic exhaustion semantics
3. `B3` Connector discovery + persisted snapshot replay hardening
4. `B4` Steer target resolution + lifecycle diagnostics hardening

## B1) Multi-Child Delegation Queueing

### Goal

Extend child orchestration beyond single-child thin slice while keeping deterministic replay.

### Scope

- Allow bounded multi-child configuration:
  - `max_children = 2`
  - `max_active_children = 1`
- Freeze queue ordering by persisted queue key:
  - `child.queue_seq` assigned monotonically at spawn
  - FIFO dispatch by `(parent_session_id, queue_seq ASC)`
- Keep parent-child linkage explicit in runtime events/artifacts.
- Keep `URM_CHILD_QUEUE_MODE` compatibility behavior explicit (`v1`, `v2`).

### Locks

- Queue scheduling decisions must be deterministic for identical parent stream state.
- Spawn/cancel endpoints remain idempotent by `client_request_id`.
- No best-effort emulation path when child capability is unavailable.
- Queued cancel semantics are frozen:
  - cancel removes queued child deterministically.
  - if capacity exists, next queued dispatch occurs immediately after cancel processing.
  - event ordering is frozen:
    - queued cancel event (`WORKER_CANCEL`) must be appended before any subsequent dispatch start (`WORKER_START` with `status=running`).
  - stream placement is frozen:
    - queued-child cancel appends to child stream.
    - parent stream appends linkage note for the same cancel operation.
- Queue sequencing and idempotency coupling are frozen:
  - `queue_seq` is unique/monotonic per `parent_session_id`.
  - same `client_request_id` replay returns the same `child_id` and same assigned `queue_seq`.
  - same `client_request_id` with different payload fails closed via deterministic idempotency conflict containing both payload hashes in context.
- Queue-mode migration lock is frozen:
  - post-vNext+5 default mode on `main` is `URM_CHILD_QUEUE_MODE=v2`.
  - `v1` compatibility remains explicit:
    - hard cap single child.
    - queue attempts fail closed with deterministic child-limit code.

### Acceptance

- Identical spawn request sequences replay to identical child lifecycle ordering.
- Queue replay preserves FIFO order across retries/restarts.
- Queue + cancel race fixture passes:
  - child A running, child B queued, cancel A, B dispatches deterministically.

## B2) Budget Inheritance + Exhaustion Semantics

### Goal

Freeze deterministic budget behavior across parent and child runs.

### Scope

- Add/freeze `budget.v1` snapshot semantics on child spawn:
  - `budget_version = "budget.v1"`
  - `max_duration_secs`
  - `max_token_budget`
  - `max_solver_calls`
- Enforce deterministic budget exhaustion outcomes and terminal signals.

### Locks

- Child budget snapshot is immutable after spawn.
- Mid-run parent policy/profile changes do not mutate existing child budget snapshots.
- Budget measurement sources are frozen:
  - duration:
    - replay evaluates from persisted child lifecycle timestamps/events only.
    - live mode may observe wall-clock, but observed timestamps must be emitted so replay reproduces the same decision.
  - token budget:
    - enforcement is allowed only with authoritative usage signal.
    - if authoritative token usage is unavailable, set `token_usage_unobserved=true` and do not hard-enforce token budget.
  - solver calls:
    - counted from deterministic persisted child-run counters/events only.
- Budget breach behavior is frozen:
  - fail closed with deterministic `URM_CHILD_BUDGET_EXCEEDED`.
  - include breach dimension in context:
    - `dimension = duration | tokens | solver_calls`.
  - include deterministic `limit` and `observed` fields in context.
  - append deterministic terminal event to child stream before terminalization.

### Acceptance

- Budget breach scenarios replay with stable error/event outcomes.
- Child snapshot immutability is proven by fixture reruns.
- Deterministic budget-breach fixture passes across restart/replay.

## B3) Connector Discovery + Snapshot Replay

### Goal

Make connector discovery replay-safe and governed by persisted snapshots.

### Scope

- Harden connector discovery flow:
  - live discovery only in live mode.
  - persisted `connector_snapshot@1` evidence for replay.
- Freeze replay resolution:
  - replay mode resolves by `connector_snapshot_id` only.
- Add deterministic connector exposure mapping layer:
  - raw snapshot evidence remains unfiltered.
  - filtered/exposed connector view is derived from a versioned local mapping registry:
    - `connector_exposure_mapping.v1.json`.

### Locks

- No live `app/list` reads in replay mode.
- Replay-mode live-read attempts fail closed with deterministic connector code.
- Raw connector snapshot semantics are frozen:
  - snapshot artifact is evidence-only and unfiltered.
- Filtered connector exposure semantics are frozen:
  - any filtered "exposed connectors" view must be driven by versioned local mapping registry + capability/policy checks.
  - mapping evaluation order is deterministic (sorted rules with frozen first-match/priority semantics).
  - filtered output is canonical sorted by `connector_id ASC`.
  - filtered-out connectors in derived view must include deterministic `deny_reason_code`.
- Any action depending on connectors must include `connector_snapshot_id` in action payload hash.
- Stale predicate is frozen:
  - stale if requested capability snapshot id mismatches persisted snapshot capability id, OR
  - stale if `snapshot.created_at < min_acceptable_ts` when `min_acceptable_ts` is provided.
  - `snapshot.created_at` provenance is frozen to the persisted artifact field value (never filesystem mtime or live clock lookup).
- Missing/stale/live-read-blocked paths must emit deterministic evidence events with reason and code context.

### Acceptance

- Connector discovery replay is deterministic for identical snapshot ids.
- Snapshot-not-found/stale paths are deterministic and auditable.
- Replay mode rejects live discovery attempts deterministically.

## B4) Steer Target Resolution + Lifecycle Diagnostics

### Goal

Strengthen steer targeting and diagnostics without introducing non-determinism.

### Scope

- Freeze steer target semantics:
  - `turn_id` preferred.
  - `last_turn` allowed only as deterministic alias.
- Emit deterministic steer outcomes:
  - `STEER_APPLIED`
  - `STEER_DENIED`

### Locks

- `last_turn` alias resolution algorithm is frozen:
  - resolve to greatest persisted turn id in parent stream state up to a deterministic boundary sequence.
  - boundary sequence is `request.after_seq` when provided.
  - in live mode when `request.after_seq` is omitted, boundary sequence is current persisted parent stream tail.
  - steer outcome events must include `resolved_against_seq`.
  - if unresolved, fail deterministically with `URM_STEER_TARGET_UNRESOLVED`.
- Steer outcome event symmetry is frozen:
  - both allow and deny paths append explicit steer outcome events.
- Endpoint code mapping is frozen:
  - primary family: `URM_STEER_*`.
  - common envelope compatibility remains allowed:
    - `URM_POLICY_DENIED`
    - `URM_NOT_FOUND`
    - idempotency conflict code.
- Target-resolution behavior is deterministic for identical event streams.
- Diagnostics are additive-only and do not alter existing solver/governance semantics.

### Acceptance

- Steer replay preserves target resolution and emitted outcomes.
- Unresolved target paths emit stable deterministic failure code and event.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Endpoint/code mapping stays explicit:
  - steer endpoint -> `URM_STEER_*` (plus common envelope compatibility)
  - spawn/cancel endpoints -> `URM_CHILD_*`
  - connector snapshot flows -> `URM_CONNECTOR_*`
- Suggested stable additions for this arc:
  - `URM_CHILD_BUDGET_EXCEEDED`
  - `URM_CONNECTOR_REPLAY_LIVE_READ_BLOCKED`
  - `URM_STEER_TARGET_UNRESOLVED`

## Proposed Commit Plan (Draft)

1. `runtime: harden v2 child queue ordering key, cancel/dispatch ordering, and mode migration defaults`
2. `runtime: add budget.v1 measurement-source locks and deterministic breach enforcement`
3. `runtime: harden connector replay-only resolution, exposure mapping registry, and stale predicate`
4. `runtime: harden steer target alias resolution and deny-path event symmetry`
5. `tests: add queue-cancel race and budget-breach replay fixtures plus restart/idempotency coverage`

## Proposed Exit Criteria (Draft)

- B1-B4 merged with green CI.
- Multi-child queue replay determinism is `100%` on locked fixtures.
- Queue-cancel race fixture is byte-identical across replay reruns.
- Budget exhaustion code/event stability is `100%` on locked fixtures.
- Connector snapshot replay determinism is `100%` for identical snapshot ids.
- Replay mode live-discovery blocking is deterministic and evented.
- Steer target resolution replay determinism is `100%` on locked fixtures.
- `STEER_APPLIED` / `STEER_DENIED` event outcomes are deterministic and auditable.
- No solver-semantics delta and no trust-lane regression introduced.
