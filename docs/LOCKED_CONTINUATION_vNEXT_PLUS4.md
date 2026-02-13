# Locked Continuation vNext+4 (Frozen)

This document freezes the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS3.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v1.md`

Status: frozen.

Decision basis:

- vNext+3 exit criteria passed on `main` (D1-D4 complete, CI green).
- Remaining option tracks from `DRAFT_NEXT_ARC_OPTIONS_v1.md` are A and B.
- This arc selects **Option A deepening only**.
- Option B deepening is explicitly deferred to the next arc (`vNext+5`) to keep execution lanes separate.

## Global Locks

- No solver semantic changes in this arc.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- All new behavior is additive-only unless explicitly marked breaking (none in this arc).
- Determinism and replayability remain mandatory for all new outputs and tests.
- Runtime behavior must emit evidence events in `urm-events@1`.
- Versioned governance artifacts in this arc must have explicit JSON Schema files under `spec/`:
  - `policy_explain@1`
  - `incident_packet@1`
  - `policy_activation_log@1`
- Versioned governance inputs/registries introduced in this arc must also have explicit JSON Schema files under `spec/`:
  - `policy/profiles.v1.json`
  - `policy/incident_redaction_allowlist.v1.json`
  - `policy_registry@1`
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - explicit `evaluation_ts` input OR fixed deterministic default only.
- New `/urm/...` endpoints in this arc must be idempotent via `client_request_id`.
- Policy/runtime governance outputs must be reproducible from persisted artifacts only:
  - no live environment/process state reads for deterministic decisions/reports.
- Governance operation event names are explicit and frozen:
  - `PROFILE_SELECTED`
  - `PROFILE_DENIED`
  - `POLICY_MATERIALIZED`
  - `POLICY_MATERIALIZE_DENIED`
  - `POLICY_ROLLED_OUT`
  - `POLICY_ROLLED_BACK`
- Event placement is frozen:
  - policy/profile/rollout events append to the governed action stream.
  - governed action stream for rollout/rollback is `urm_policy:<profile_id>`.
  - profile selection inside a running session appends to the session stream only.
  - profile selection outside session context appends to `urm_policy:<profile_id>`.
  - policy materialization events append to `urm_policy_registry`.
  - parent lifecycle events append to parent stream.
  - child lifecycle/run events append to child stream with parent linkage.
  - fallback when parent stream is unavailable remains `urm_audit:<parent_session_id>`.

## Arc Scope (Frozen)

This arc implements only:

1. `A1` Policy explain operational hardening
2. `A2` Profile-pack lifecycle hardening
3. `A3` Incident packet deterministic forensics hardening
4. `A4` Policy rollout/rollback controls by `policy_hash`
5. `A5` Governance evidence template + decision-prep scaffold

## A1) Policy Explain Operational Hardening

### Goal

Make policy explain outputs operator-ready while preserving strict deterministic behavior.

### Scope

- Keep existing `policy explain --policy --context` path as additive-compatible.
- Add forensic explain path from persisted decisions:
  - `policy explain-from-decision --decision <path-or-id>`
- Harden explain rendering around persisted `PolicyDecision`/trace inputs.
- Keep JSON as authoritative output contract:
  - `policy_explain@1`
- Keep markdown rendering as derived/non-authoritative:
  - generated only from `policy_explain@1` payload.
- Add deterministic input manifest fields in explain output:
  - `policy_hash`, `input_context_hash`, `evaluation_ts`, evidence refs.

### Locks

- `policy eval` remains the authoritative decision engine.
- `policy explain` never uses alternate decision logic.
- `policy explain --policy --context` may call the authoritative `policy eval` engine only to obtain `PolicyDecision` trace inputs before rendering.
- `policy explain` timestamp behavior is frozen:
  - deterministic mode uses explicit `--evaluation-ts` or fixed default `1970-01-01T00:00:00Z`.
  - wall-clock mode is explicit opt-in (`--use-now`) and non-deterministic by contract.
- Deterministic mode may not read live runtime/environment state.
- Output ordering is deterministic and canonicalized.
- If path metadata is emitted (`input_policy`, `input_context`), it is non-semantic.
- Determinism anchors for explain are hash-based:
  - `policy_hash`
  - `input_context_hash`
  - decision/evidence hashes where applicable.

### Acceptance

- Same explain inputs yield byte-identical `policy_explain@1`.
- Markdown rendering hash is stable for identical JSON explain payloads.
- Explain outputs validate against versioned schema and include required hashes.

## A2) Profile-Pack Lifecycle Hardening

### Goal

Make policy profiles operationally safe and replay-deterministic for session/run governance.

### Scope

- Harden profile model with explicit persisted fields:
  - `profile_id`, `profile_version`, `policy_hash`
- Freeze profile-policy source-of-truth registry:
  - `policy/profiles.v1.json` mapping:
    - `profile_id`
    - `profile_version`
    - `default_policy_hash`
    - `allowed_policy_hashes`
    - `policy_ref`
- Harden profile selection/retrieval surfaces:
  - `policy profile list`
  - `policy profile select`
  - `policy profile current`
- Add replay-visible profile events:
  - `PROFILE_SELECTED`
  - `PROFILE_DENIED`

### Locks

- Profile selection is explicit and evented (no hidden fallback).
- Unknown/missing profile fails closed with deterministic policy code.
- Error-code semantics are frozen:
  - `URM_POLICY_PROFILE_NOT_FOUND`: profile id does not exist in profile registry.
  - `URM_POLICY_PROFILE_DENIED`: profile exists but caller/session is not authorized to select it.
- Source-of-truth semantics are frozen:
  - `policy_hash` is authoritative for activation/state resolution.
  - `policy_ref` is convenience-only for local materialization workflows.
  - runtime active-policy resolution never loads policy by `policy_ref`.
- Active policy source-of-truth is frozen:
  - active policy for a profile is always derived from `policy_activation_log@1`.
  - if profile has no activation entries yet, active policy defaults to `default_policy_hash` from `policy/profiles.v1.json`.
- Profile selection policy is driven only by the frozen profile registry mapping.
- Profile changes apply to future decisions/spawns only.
- Existing child agents keep inherited snapshot from spawn time.

### Error Codes (Frozen)

- `URM_POLICY_PROFILE_NOT_FOUND`
- `URM_POLICY_PROFILE_DENIED`
- `URM_POLICY_PROFILE_MAPPING_INVALID`

### Acceptance

- Profile selection is replay-deterministic for identical inputs.
- Child snapshot inheritance remains immutable after later parent profile switches.
- Profile event stream linkage is deterministic and auditable.

## A3) Incident Packet Deterministic Forensics Hardening

### Goal

Strengthen `incident_packet@1` as deterministic, cross-stream forensic evidence.

### Scope

- Keep authoritative schema `incident_packet@1` (additive-only extension).
- Enforce deterministic ordering and canonical refs:
  - `streams` sorted by `stream_id` ascending.
  - `artifact_refs` sorted lexicographically by `(kind, ref)`.
  - canonical ref formats:
    - `event:<stream_id>#<seq>`
    - `artifact:<artifact_id>`
- Harden redaction via deterministic allowlist/markers.

### Locks

- Incident packets are reconstructed from persisted artifacts only.
- Redaction policy is explicit and deterministic:
  - `policy/incident_redaction_allowlist.v1.json` defines redaction-eligible fields.
  - output redaction markers are deterministic and sorted.
- No secrets/env dumps may appear in incident packets.
- Unknown incident fields outside the redaction allowlist fail closed with `URM_INCIDENT_PACKET_BUILD_FAILED`.
- Allowlist/schema evolution rule is frozen:
  - any incident schema field addition requires same-PR allowlist version bump and fixture updates.
- Cross-stream incidents remain first-class via `streams: list[{stream_id, seq_range}]`.

### Error Codes (Frozen)

- `URM_INCIDENT_PACKET_BUILD_FAILED`
- `URM_INCIDENT_PACKET_INVALID_REF`

### Acceptance

- Same evidence inputs yield byte-identical incident packet output.
- Reconstructed packet reproduces `decision_code` + `matched_rule_ids`.
- Redaction output is deterministic across reruns.
- Secret-leak guard tests pass on fixture corpus and fail closed on violations.

## A4) Policy Rollout/Rollback Controls by `policy_hash`

### Goal

Provide auditable, deterministic policy activation controls without rewriting evidence history.

### Scope

- Add explicit policy state surfaces:
  - `POST /urm/policy/rollout`
  - `POST /urm/policy/rollback`
  - `GET /urm/policy/active?profile_id=<profile_id>`
- Persist append-only activation log artifact:
  - `policy_activation_log@1`
- Persist policy materialization registry:
  - `policy_registry@1` canonical policy payloads keyed by `policy_hash`
- Add deterministic policy materialization ingest surface:
  - `policy materialize --policy <path>`
- Add deterministic CLI wrappers:
  - `policy rollout`
  - `policy rollback`

### Locks

- `POST` rollout/rollback are idempotent via `client_request_id`.
- Rollout/rollback events append to profile-scoped governance stream:
  - `urm_policy:<profile_id>`
- Rollout/rollback scope is per-profile, not global:
  - payload must include `profile_id`.
  - rollback target resolution is constrained to that profile history.
- Same `client_request_id` + identical payload returns same activation result.
- Same `client_request_id` + different payload fails deterministically.
- Idempotency conflict check is hash-based:
  - persist `request_payload_hash` for each `client_request_id`.
  - `request_payload_hash` excludes non-semantic request fields:
    - `activation_ts`
    - operator note/message fields (if present)
  - on mismatch return deterministic conflict with both hashes in context.
- Rollback semantics are explicit-target only:
  - request must include `target_policy_hash`.
  - rollback target must reference an existing prior `policy_hash` in the same profile history.
- Rollout targets must reference materialized policy payload in `policy_registry@1`.
- Rollout governance allowlist is profile-scoped and fail-closed:
  - rollout target hash must be present in `allowed_policy_hashes` for the target `profile_id`.
  - rollout is denied deterministically when hash is not allowed for that profile.
- Materialization ingest invariants are frozen:
  - canonical policy hash is recomputed at ingest.
  - ingest fails closed when claimed hash (if provided) does not match computed hash.
- `policy materialize` timestamp behavior is frozen:
  - deterministic mode uses explicit `--materialize-ts` or fixed default `1970-01-01T00:00:00Z`.
  - wall-clock mode is explicit opt-in (`--use-now`) and non-deterministic by contract.
- Historical evidence is immutable; rollback appends events, never rewrites history.
- Running parent/child sessions keep captured policy snapshot; no mid-run mutation.
- Activation log minimum fields are frozen:
  - `activation_seq`
  - `client_request_id`
  - `request_payload_hash`
  - `profile_id`
  - `action` (`rollout` | `rollback`)
  - `target_policy_hash`
  - `prev_policy_hash`
  - `activation_ts`
- `activation_ts` mode is frozen:
  - deterministic tests/replay must provide explicit `activation_ts`.
  - live mode may use server-assigned wall-clock timestamp.

### Error Codes (Frozen)

- `URM_POLICY_ROLLOUT_CONFLICT`
- `URM_POLICY_ROLLBACK_TARGET_NOT_FOUND`
- `URM_POLICY_IDEMPOTENCY_CONFLICT`
- `URM_POLICY_UNKNOWN_HASH`
- `URM_POLICY_ROLLOUT_HASH_NOT_ALLOWED`

### Endpoint/Code Mapping Lock

- `/urm/policy/rollout` and `/urm/policy/rollback` emit `URM_POLICY_*` codes.
- Common envelope compatibility remains:
  - `URM_POLICY_DENIED`
  - `URM_NOT_FOUND`

### Acceptance

- Rollout/rollback replay is deterministic for identical activation logs.
- Idempotency behavior is stable across retries and process restarts.
- Active policy state is reconstructable from append-only activation history.
- Active policy state resolution is deterministic per `profile_id`.
- In-flight run behavior is stable under rollout:
  - no retroactive mutation of already-running parent/child snapshots.

## A5) Governance Evidence Template + Decision Prep

### Goal

Standardize closeout evidence capture for A deepening and prepare B deepening decision input.

### Scope

- Add docs template:
  - `docs/templates/GOVERNANCE_OPS_DEEPENING_EVIDENCE_REPORT_TEMPLATE.md`
- Add draft decision scaffold:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS4.md`

### Locks

- Claims in evidence report must be backed by generated artifacts.
- Decision scaffold is draft-only and may not pre-commit B scope before thresholds are measured.

### Acceptance

- Template and scaffold exist, are reproducible, and reference concrete artifact fields/paths.

## Error-Code Policy (Frozen)

- Reuse existing URM/common codes where applicable.
- New codes are allowed only when needed, must be deterministic, and must be prefixed `URM_`.
- No fork of URM error envelope or event taxonomy.

## Commit Plan (Small Green Commits)

1. `governance: harden policy_explain@1 deterministic rendering and input manifest`
2. `governance: harden profile lifecycle model/events plus profiles.v1 policy mapping`
3. `forensics: harden incident_packet@1 deterministic ordering and redaction markers`
4. `runtime: add profile-scoped policy rollout/rollback with policy registry and idempotent activation log`
5. `tests: add replay/idempotency fixtures for explain profile incident rollout`
6. `docs: add governance deepening evidence template and stop-gate decision scaffold`

## PR Sequence (Frozen)

1. **PR1: Explain Hardening**
   - A1 `policy_explain@1` determinism + schema tests
2. **PR2: Profile Lifecycle**
   - A2 profile packs, selection/current/list, lifecycle events
   - frozen profile-to-policy registry mapping
3. **PR3: Incident Forensics**
   - A3 deterministic `incident_packet@1` hardening
4. **PR4: Rollout/Rollback**
   - A4 profile-scoped policy activation controls + policy materialization + idempotency + replay tests
5. **PR5: Docs + Closeout Scaffolds**
   - A5 evidence template + draft stop-gate decision note

## Exit Criteria

- A1-A5 merged with green CI.
- `policy_explain@1` determinism is `100%` on locked fixtures.
- Profile selection/lifecycle replay determinism is `100%` on locked fixtures.
- Incident packet reconstruction reproducibility is `>= 99%`.
- Rollout/rollback replay determinism and idempotency are `100%` on locked fixtures.
- No solver-semantics delta and no trust-lane regression introduced.
- Follow-on lock draft for Option B deepening is ready.
