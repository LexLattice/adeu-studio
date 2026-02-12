# Draft Next Arc Options v1

This document proposes continuation options after completing:

- `LOCKED_CONTINUATION_vNEXT.md`
- `LOCKED_INSTRUCTION_KERNEL_v0.md`
- `LOCKED_CROSS_REPO_IMPORTS_v0.md`

Status: draft only (not frozen).  
Goal: choose the next locked arc with clear tradeoffs.

## Baseline Snapshot

Current baseline includes:

- Instruction policy IR + deterministic evaluator + policy traces/events.
- Codex dynamics thin slice (`/urm/copilot/steer`, child spawn/cancel lifecycle).
- Second domain portability proof (`urm_domain_paper`).
- Semantic depth v2 baseline (`concepts.tscore.v2`, bridge-loss-aware metadata).

The system is now governance-capable, replay-capable, and domain-extensible.

## Shared Locks For Any Next Arc

- No solver semantic changes unless explicitly versioned and locked.
- Trust lanes remain explicit and separate (`mapping_trust`, `solver_trust`, `proof_trust`).
- New endpoints are additive and idempotent where applicable.
- Replay-mode determinism is mandatory for acceptance tests.
- New runtime behavior must emit evidence and fit `urm-events@1`.
- Determinism claims are relative to recorded snapshot inputs:
  - `(policy_hash, input_context_hash, capability_snapshot_id, connector_snapshot_id?)`.
- Snapshot IDs used for deterministic claims must be persisted evidence artifacts, not live runtime lookups.
- `capability_snapshot_id` is grounded to persisted capability probe/snapshot artifacts:
  - v1 may reuse current probe artifact id.
  - if a dedicated snapshot artifact is introduced, it must be versioned and evidence-linked.
- For connector-aware paths, `connector_snapshot_id` is mandatory (not optional).
- Hidden wall-clock behavior is forbidden in deterministic mode:
  - time must be explicit input (`evaluation_ts`) or fixed deterministic default.
- Event stream placement is explicit:
  - policy events append to the same stream as the governed action.
  - parent lifecycle and steer events append to parent stream.
  - child runtime events append to child stream with deterministic parent linkage refs.

## Option A: Governance Ops v1.1

### Goal

Move policy and runtime governance from "implemented" to "operationally mature."

### Scope

1. `policy explain` command with deterministic trace rendering.
2. Policy profile packs: `safe_mode`, `default`, `experimental`.
3. Deterministic incident packet generation from evidence + policy trace.
4. Explicit rollout/rollback controls by `policy_hash`.
5. Structured output contracts:
   - `policy_explain@1`
   - `incident_packet@1`

### Locks

- Explain output is advisory and non-semantic.
- Profile selection is explicit and evented (no implicit fallback).
- Incident packet is reproducible from persisted artifacts only.
- Rollback is deterministic and never rewrites historical evidence.
- `policy explain` authoritative output is JSON schema `policy_explain@1`; optional markdown views are derived and non-authoritative.
- `policy eval` remains the authoritative decision engine.
- `policy explain` is a deterministic rendering/forensics layer over `PolicyDecision` and related evidence, not a replacement for `policy eval`.
- `policy explain` deterministic mode must not read live runtime state outside explicit inputs:
  - semantic policy form
  - policy trace
  - explicit evaluation context.
- Profile storage is server-side and scoped per session/run.
- Missing/unknown profile fails closed with deterministic policy code.
- Child agents keep inherited profile snapshot from spawn time (no mid-run profile mutation).
- Profile model is explicit:
  - `profile_id`, `profile_version`, `policy_hash` are persisted in session/run governance state.
- `incident_packet@1` minimum fields:
  - `policy_hash`, `input_context_hash`, `decision_code`, `matched_rule_ids`, `artifact_refs`.
  - `streams: list[{stream_id, seq_range}]` for cross-stream incidents (parent/child).
- Incident packet includes deterministic redaction markers and must not include secrets/env dumps.
- Suggested stable Option A error-code set:
  - `URM_POLICY_EXPLAIN_INVALID_INPUT`
  - `URM_POLICY_PROFILE_NOT_FOUND`
  - `URM_INCIDENT_PACKET_BUILD_FAILED`

### Acceptance

- Same policy/context yields byte-identical `policy explain` output.
- Profile switch events are replayable and tied to session/run context.
- Incident packet reconstruction matches recorded decision code and matched rules.
- `policy_explain@1` and `incident_packet@1` validate against versioned schemas.

### Risk

- Can become tooling-heavy before visible user-facing gains.

## Option B: Codex Dynamics v2

### Goal

Expand interactive orchestration beyond thin-slice steer + single child.

### Scope

1. Controlled multi-child delegation (`max_children > 1`, queueing policy).
2. Parent-child budget inheritance and exhaustion semantics.
3. App connector discovery (`app/list`, `app/list/updated`) with policy filtering.
4. Stronger steer targeting and lifecycle diagnostics.
5. Deterministic connector snapshot flow:
   - live discovery -> persisted `connector_snapshot@1` -> replay/eval by snapshot id.

### Locks

- No best-effort emulation for missing capabilities.
- Delegation limits and budget checks are deny-first and deterministic.
- Child actions inherit parent policy snapshot unless explicitly versioned override.
- App connectors are visible only through capability lattice + instruction policy.
- New dynamics endpoints are idempotent via `client_request_id`:
  - spawn, steer, cancel.
- N2 endpoint namespace is explicit:
  - `POST /urm/copilot/steer`
  - `POST /urm/agent/spawn`
  - `POST /urm/agent/{child_id}/cancel`
- Queueing policy is deterministic:
  - server-assigned parent `seq` order.
  - FIFO dispatch by `seq`.
  - freeze `max_children = 2`, `max_active_children = 1` in thin slice.
- Migration lock from current `max_children = 1` baseline:
  - gated behind a versioned runtime flag.
  - replay fixtures are versioned/migrated with explicit compatibility notes.
- Budget semantics are explicit and versioned:
  - `budget.v1` fields include `max_duration_secs`, `max_token_budget`, `max_solver_calls`.
  - hard-limit breaches produce deterministic terminal events/codes.
- Child spawn captures immutable governance snapshot:
  - `policy_hash`, profile, capability facts, budget snapshot.
- Steer request target is stable:
  - `turn_id` preferred.
  - `last_turn` allowed only as deterministic server-resolved alias.
- Steer outcome events are explicit:
  - `STEER_APPLIED` or `STEER_DENIED` with `target_turn_id`.
- Connector discovery replay contract:
  - replay uses persisted `connector_snapshot_id` only.
  - no live `app/list` calls in replay mode.
- Suggested stable Option B error-code set:
  - `URM_STEER_TARGET_UNRESOLVED`
  - `URM_STEER_DENIED`
  - `URM_CHILD_QUEUE_LIMIT_EXCEEDED`
  - `URM_CHILD_BUDGET_EXCEEDED`
  - `URM_CONNECTOR_SNAPSHOT_NOT_FOUND`
  - `URM_CONNECTOR_SNAPSHOT_STALE`
- Endpoint/code mapping lock:
  - steer endpoint emits `URM_STEER_*` codes only.
  - spawn/cancel endpoints emit `URM_CHILD_*` codes only.
  - connector snapshot flows emit `URM_CONNECTOR_*` codes only.

### Acceptance

- Multi-child replay is deterministic with stable ordering and linkage.
- Budget breaches produce stable codes and deterministic terminal events.
- Connector discovery is deterministic for identical capability snapshots.
- Queue replay must preserve FIFO order for identical parent stream and spawn request sequence.

### Risk

- Highest runtime complexity and protocol drift surface.

## Option C: Portability Proof v2

### Goal

Prove URM portability with stronger cross-domain pressure.

### Scope

1. Harden `DomainToolPack` protocol and registration API.
2. Add one additional compact domain pack beyond `paper.abstract`:
   - frozen pilot candidate: `doc.digest` (closed-world, local text only).
3. Run cross-domain policy/evidence/replay conformance suite.
4. Publish transfer report v2 with coupling deltas.

### Locks

- `urm_runtime` stays domain-agnostic.
- No new domain forks of URM event/error taxonomy.
- Generic runtime primitives require at least two-domain justification.
- Domain packs cannot import ADEU domain internals.
- Portability v2 domain expansion remains closed-world:
  - local provided inputs only.
  - no network/browsing/citation retrieval.
- Conformance suite must run offline and deterministic:
  - no live Codex login dependency.
  - no live connector enumeration.
  - fixture/snapshot driven execution only.

### Acceptance

- Two non-ADEU domains complete end-to-end runs under same policy controls.
- Import-audit confirms no new ADEU coupling in runtime core.
- Conformance suite passes for event schema, policy evaluation, replay.
- Offline conformance suite passes in CI without network access.

### Risk

- Domain selection can stall momentum if scope is too broad.

## Option D: Semantic Depth v2.1

### Goal

Improve repair quality and interpretability on top of current deterministic core.

### Scope

1. Question quality v3 (dedupe/ranking/rationale tightening).
2. Tournament objective tuning with locked deterministic tie-break provenance.
3. Cross-artifact coherence diagnostics and drift surfacing.
4. Quality dashboard extension with explicit before/after deltas.

### Locks

- Bridge loss remains informational.
- LLM-derived signals cannot override deterministic evidence dimensions.
- Score/rank versions are explicit and emitted in all ranking artifacts.
- Replay mode remains authoritative for acceptance.
- Tournament artifacts include explicit:
  - `objective_vector_version`
  - `tie_break_version`
  - `score_version`
- Quality dashboard deltas are computed from locked fixture suites only, never live runs.

### Acceptance

- Eval fixtures show measurable redundancy reduction vs baseline.
- Ranking is deterministic in replay mode.
- Coherence diagnostics are permutation-invariant on fixture permutations.
- Ranking artifacts include versioned tie-break metadata on every emitted result.

### Risk

- Easy to drift into subjective quality work without strict eval discipline.

## Decision Matrix

### If priority is reliability under scale

- Choose Option A first.

### If priority is product differentiation via agent dynamics

- Choose Option B first.

### If priority is proving platform thesis

- Choose Option C first.

### If priority is immediate reasoning quality gains

- Choose Option D first.

## Recommended Sequence (Draft)

1. Option A thin slice:
   - `policy explain`
   - incident packet v1
2. Option B thin slice:
   - bounded multi-child (`max_children = 2`, `max_active_children = 1`, FIFO queue)
   - connector discovery snapshot flow (`connector_snapshot@1`, read-only filtered usage)
3. Reassess using metrics, then pick Option C or D as primary arc.

Why:

- A makes governance changes safer.
- B gives visible runtime product gains.
- C or D then optimize for strategic thesis (`portability` vs `semantic quality`).

## Proposed Freeze Candidate (Next Step)

Create `docs/LOCKED_CONTINUATION_vNEXT_PLUS1.md` with:

1. one thin slice from Option A,
2. one thin slice from Option B,
3. explicit stop gate for choosing C vs D based on measured outcomes.

Suggested measured outcomes:

- policy incident reproducibility rate >= 99%
- child lifecycle replay determinism rate = 100% on fixtures
- runtime failure-code stability = 100% code-consistency across replay reruns
- connector snapshot replay stability = 100% for identical snapshot ids
- quality delta on existing eval fixtures is non-negative for primary ranking metrics
