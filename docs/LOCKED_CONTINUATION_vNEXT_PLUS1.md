# Locked Continuation vNext+1 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT.md`
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md`
- `docs/LOCKED_CROSS_REPO_IMPORTS_v0.md`

Status: frozen.

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new API behavior is additive-only.
- New `/urm/...` endpoints must be idempotent via `client_request_id`.
- Determinism claims are relative to persisted snapshot inputs:
  - `policy_hash`
  - `input_context_hash`
  - `capability_snapshot_id`
  - `connector_snapshot_id` (mandatory for connector-aware paths)
- Hidden wall-clock behavior is forbidden in deterministic mode.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Event placement is frozen:
  - policy events go to the governed action stream
  - steer and parent lifecycle events go to parent stream
  - child runtime events go to child stream with deterministic parent linkage
  - if parent stream is unavailable, use `urm_audit:<parent_session_id>`
- Common endpoint error set allowed for all arc endpoints:
  - `URM_POLICY_DENIED`
  - `URM_NOT_FOUND`
  - `URM_CAPABILITY_MISSING` (if capability-deny is modeled separately)
  - framework validation `422` responses

## Arc Scope (Frozen)

This arc implements only:

1. `A-thin` Governance Ops (`policy explain` + `incident_packet@1`)
2. `B-thin` Codex Dynamics (`max_children=2` with deterministic queue + connector snapshot flow)
3. Stop gate deciding whether `Portability v2` or `Semantic Depth v2.1` is next

## A-thin: Governance Ops

### Goal

Operationalize policy forensics without changing policy semantics.

### Scope

- Add `policy explain` command.
- Add `incident packet` builder.
- Add minimal server-side profile model (`safe_mode`, `default`, `experimental`) for session/run governance state.

### Locks

- `policy eval` remains authoritative decision engine.
- `policy explain` is a deterministic rendering layer over `PolicyDecision` + evidence.
- `policy explain` authoritative schema is `policy_explain@1`; markdown output is derived/non-authoritative.
- `policy explain` is a deterministic rendering/forensics layer over `PolicyDecision` and evidence; it does not replace `policy eval`.
- `incident packet` authoritative schema is `incident_packet@1`.
- `incident_packet@1` must support cross-stream incidents with:
  - `streams: list[{stream_id, seq_range}]`
- `incident_packet@1` minimum fields:
  - `policy_hash`
  - `input_context_hash`
  - `decision_code`
  - `matched_rule_ids`
  - `artifact_refs`
  - `streams`
- Redaction is deterministic and must not include secrets/env dumps.
- `incident_packet@1` deterministic ordering/ref lock:
  - `streams` sorted by `stream_id ASC`
  - `artifact_refs` sorted by `(kind, ref) ASC`
  - canonical refs use:
    - `event:<stream_id>#<seq>`
    - `artifact:<artifact_id>`
    - `run:<run_id>`
    - `validator:<validator_run_id>`
    - `proof:<proof_id>`
- Profiles are persisted server-side per session/run.
- Missing/unknown profile fails closed.
- Child agents inherit profile snapshot at spawn and do not mutate on later parent profile change.
- Profile scope/event lock:
  - profile selection is session-scoped by default, with optional run-scoped override
  - profile changes affect only future actions/spawns
  - profile events are frozen to `PROFILE_SELECTED` and `PROFILE_DENIED`

### Error Codes (Frozen)

- `URM_POLICY_EXPLAIN_INVALID_INPUT`
- `URM_POLICY_PROFILE_NOT_FOUND`
- `URM_INCIDENT_PACKET_BUILD_FAILED`

### Acceptance

- Same policy/context/evidence inputs produce byte-identical `policy_explain@1`.
- `incident_packet@1` rebuild from recorded evidence reproduces decision code and matched rules.
- Profile switch events are replayable and stream-linked.

## B-thin: Codex Dynamics v2

### Goal

Extend delegation safely with deterministic queue semantics and replayable connector discovery.

### Scope

- Extend child delegation from `max_children=1` to:
  - `max_children=2`
  - `max_active_children=1`
  - FIFO queue by server sequence.
- Keep existing dynamics endpoints and add connector snapshot flow:
  - `POST /urm/connectors/snapshot`
  - `GET /urm/connectors/snapshot/{snapshot_id}`
- Keep existing endpoints:
  - `POST /urm/copilot/steer`
  - `POST /urm/agent/spawn`
  - `POST /urm/agent/{child_id}/cancel`

### Locks

- No best-effort emulation for missing capabilities.
- Queue ordering is deterministic by server-assigned parent `seq`.
- Migration from prior `max_children=1` is behind a versioned runtime flag.
- Replay fixtures are versioned with compatibility notes for queue migration.
- Restart/recovery lock for queued/running child state:
  - after API restart, prior-process `running` or `queued` child states are marked terminal with `URM_CHILD_TERMINATED_ON_RESTART`
  - no implicit queue/run resume across process restart
  - follow-up execution requires explicit re-spawn
- Budgets use versioned shape `budget.v1` with:
  - `max_duration_secs`
  - `max_token_budget`
  - `max_solver_calls`
- Hard-limit breaches must produce deterministic terminal events/codes.
- Replay budget lock:
  - replay budget decisions use recorded usage facts from persisted evidence/events
  - replay must not re-estimate token/duration usage from model text
- Spawn snapshot is immutable and includes:
  - `policy_hash`
  - profile
  - capability facts
  - budget snapshot
- Steer targeting lock:
  - `turn_id` preferred
  - `last_turn` allowed only as deterministic server-resolved alias
  - outcome event is `STEER_APPLIED` or `STEER_DENIED` with `target_turn_id`
- Connector replay lock:
  - deterministic paths must use persisted `connector_snapshot_id`
  - no live `app/list` in replay mode
- `POST /urm/connectors/snapshot` idempotency lock:
  - same `client_request_id` + same snapshot inputs returns same `connector_snapshot_id`
  - same `client_request_id` + different snapshot inputs fails with deterministic conflict error
- Connector snapshot staleness/canonicalization lock:
  - stale when `snapshot.provider != requested_provider`
  - stale when `snapshot.capability_snapshot_id != requested_capability_snapshot_id`
  - optional time freshness checks are allowed only with explicit `min_acceptable_ts` input
  - connector list canonicalization is deterministic
  - `connector_snapshot_hash = sha256(canonical_json(connectors))`

### Error Codes (Frozen)

- `URM_STEER_TARGET_UNRESOLVED`
- `URM_STEER_DENIED`
- `URM_CHILD_QUEUE_LIMIT_EXCEEDED`
- `URM_CHILD_BUDGET_EXCEEDED`
- `URM_CONNECTOR_SNAPSHOT_NOT_FOUND`
- `URM_CONNECTOR_SNAPSHOT_STALE`
- `URM_CHILD_TERMINATED_ON_RESTART`

### Endpoint/Code Mapping Lock

- Primary family mapping:
  - `/urm/copilot/steer` emits `URM_STEER_*` for endpoint-specific failures
  - `/urm/agent/spawn` and `/urm/agent/{child_id}/cancel` emit `URM_CHILD_*` for endpoint-specific failures
  - connector snapshot endpoints emit `URM_CONNECTOR_*` for endpoint-specific failures
- Plus shared common endpoint error set from global locks.

### Acceptance

- Multi-child replay is deterministic and preserves FIFO queue order for identical input streams.
- Budget breach paths are deterministic and replay-stable.
- Connector snapshot replay is deterministic for identical `connector_snapshot_id`.

## Stop Gate (C vs D)

After A-thin and B-thin are merged, choose next primary arc (`Portability v2` vs `Semantic Depth v2.1`) using these thresholds:

- Policy incident reproducibility rate `>= 99%`
- Child lifecycle replay determinism rate `= 100%` on fixtures
- Runtime failure-code stability `= 100%` across replay reruns
- Connector snapshot replay stability `= 100%` for identical snapshot IDs
- Quality delta on locked eval fixtures is non-negative on primary ranking metrics

If thresholds fail, continue hardening A/B before selecting C or D.

Stop-gate computation lock:

- Metrics are computed from persisted evidence only.
- No live runtime/provider calls are allowed in stop-gate computation.
- Failure-code stability means identical replay inputs produce identical `(decision_code, terminal_event_code)` sequences.
- Emit deterministic machine-readable output:
  - `stop_gate_metrics@1` JSON artifact
  - optional markdown summary derived from JSON

## Commit Plan (Small Green Commits)

1. `governance: add policy_explain@1 command and schema validation`
2. `forensics: add incident_packet@1 builder with deterministic redaction`
3. `governance: persist profile model and profile events`
4. `dynamics: add queued multi-child with max_children=2 max_active=1`
5. `dynamics: add connector_snapshot@1 endpoints and replay wiring`
6. `tests: add replay fixtures for queue migration and connector snapshots`
7. `metrics: add stop_gate_metrics@1 generator from persisted evidence`
8. `docs: add stop-gate metrics report template`

## PR Sequence (Frozen)

1. **PR1: Governance Explain Core**
   - `policy_explain@1` command + schema validation + deterministic tests
   - include planning/freeze docs:
     - `docs/DRAFT_NEXT_ARC_OPTIONS_v1.md`
     - `docs/LOCKED_CONTINUATION_vNEXT_PLUS1.md`
2. **PR2: Incident Packet + Profiles**
   - `incident_packet@1` builder + deterministic redaction
   - server-side profile model + profile events
3. **PR3: Multi-Child Queue Migration**
   - `max_children=2`, `max_active_children=1`, FIFO ordering
   - restart terminalization + replay fixture migration
4. **PR4: Connector Snapshot Determinism**
   - snapshot endpoints + idempotency + staleness/canonicalization rules
   - replay integration and fixtures
5. **PR5: Stop-Gate Metrics**
   - `stop_gate_metrics@1` generator from persisted evidence
   - reporting template + CI wiring

## Exit Criteria

- A-thin merged with green CI and deterministic fixtures.
- B-thin merged with green CI and deterministic fixtures.
- Stop-gate metrics collected and reviewed.
- Next arc (`Portability v2` or `Semantic Depth v2.1`) selected with explicit lock document.
