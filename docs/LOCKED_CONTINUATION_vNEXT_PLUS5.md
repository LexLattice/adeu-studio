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

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none planned in thin slice).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit timestamp input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Policy/runtime governance outputs must be reproducible from persisted artifacts only:
  - no live environment/process state reads for deterministic decisions/reports.

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
- Freeze queue ordering:
  - server-assigned parent `seq`
  - FIFO dispatch by `seq`
- Keep parent-child linkage explicit in runtime events/artifacts.

### Locks

- Queue scheduling decisions must be deterministic for identical parent stream state.
- Spawn/cancel endpoints remain idempotent by `client_request_id`.
- No best-effort emulation path when child capability is unavailable.

### Acceptance

- Identical spawn request sequences replay to identical child lifecycle ordering.
- Queue replay preserves FIFO order across retries/restarts.

## B2) Budget Inheritance + Exhaustion Semantics

### Goal

Freeze deterministic budget behavior across parent and child runs.

### Scope

- Add/freeze `budget.v1` snapshot semantics on child spawn:
  - `max_duration_secs`
  - `max_token_budget`
  - `max_solver_calls`
- Enforce deterministic budget exhaustion outcomes and terminal signals.

### Locks

- Child budget snapshot is immutable after spawn.
- Budget breaches fail closed and emit deterministic `URM_CHILD_*` codes/events.
- Mid-run parent policy/profile changes do not mutate existing child budget snapshots.

### Acceptance

- Budget breach scenarios replay with stable error/event outcomes.
- Child snapshot immutability is proven by fixture reruns.

## B3) Connector Discovery + Snapshot Replay

### Goal

Make connector discovery replay-safe and governed by persisted snapshots.

### Scope

- Harden connector discovery flow:
  - live discovery only in live mode
  - persisted `connector_snapshot` evidence for replay
- Freeze replay resolution:
  - replay mode must resolve by snapshot id only.

### Locks

- No live `app/list` reads in replay mode.
- Connector visibility remains filtered through capability lattice + instruction policy.
- Missing/stale snapshot fails closed with deterministic `URM_CONNECTOR_*` codes.

### Acceptance

- Connector discovery replay is deterministic for identical snapshot ids.
- Snapshot-not-found/stale paths are deterministic and auditable.

## B4) Steer Target Resolution + Lifecycle Diagnostics

### Goal

Strengthen steer targeting and diagnostics without introducing non-determinism.

### Scope

- Freeze steer target semantics:
  - `turn_id` preferred
  - `last_turn` allowed only as deterministic alias
- Emit deterministic steer outcomes:
  - `STEER_APPLIED`
  - `STEER_DENIED`

### Locks

- Steer endpoint emits `URM_STEER_*` codes only.
- Target-resolution behavior is deterministic for identical event streams.
- Diagnostics are additive-only and do not alter existing solver/governance semantics.

### Acceptance

- Steer replay preserves target resolution and emitted outcomes.
- Unresolved target paths emit stable deterministic failure codes.

## Error-Code Policy (Draft Lock)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- Endpoint/code mapping stays explicit:
  - steer endpoint -> `URM_STEER_*`
  - spawn/cancel endpoints -> `URM_CHILD_*`
  - connector snapshot flows -> `URM_CONNECTOR_*`

## Proposed Commit Plan (Draft)

1. `runtime: add deterministic multi-child queueing limits and FIFO replay fixtures`
2. `runtime: freeze budget.v1 inheritance/exhaustion semantics with deterministic terminal codes`
3. `runtime: harden connector snapshot replay-only resolution and failure semantics`
4. `runtime: harden steer target resolution and lifecycle diagnostics`
5. `tests: add replay/idempotency fixtures for queue budget steer connector snapshot`

## Proposed Exit Criteria (Draft)

- B1-B4 merged with green CI.
- Multi-child queue replay determinism is `100%` on locked fixtures.
- Budget exhaustion code/event stability is `100%` on locked fixtures.
- Connector snapshot replay determinism is `100%` for identical snapshot ids.
- Steer target resolution replay determinism is `100%` on locked fixtures.
- No solver-semantics delta and no trust-lane regression introduced.
