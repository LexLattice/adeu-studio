# Locked Continuation vNext+37 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS36.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS36.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/SEMANTICS_v3.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+36` (`J1`-`J2`) is merged on `main` via PR `#218` and PR `#219` with green CI checks.
- `vNext+36` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS36.md` with `all_passed = true`.
- Post-v36 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`.
- Selected v37 thin-slice default is remaining boundary-release candidate:
  - `V31-G` (proposer idempotency persistence alignment).
- `vNext+37` is constrained to deterministic additive hardening for `V31-G` only:
  - no solver/runtime semantics release,
  - no additional governance boundary release expansion in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS36.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v37,
  - v37 keyset must be exactly equal to v36 keyset (set equality, derived cardinality),
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36 continuity guarantees remain frozen as release preconditions:
  - worker-route governance release contract (`V31-F`, `J1`) remains authoritative,
  - v36 governance-release guard suite (`V31-F`, `J2`) remains authoritative baseline.
- Boundary-release scope lock for v37 is frozen:
  - this arc authorizes `V31-G` persistence boundary release only,
  - no additional `L2` boundary release is authorized in this arc.
- Governance continuity lock remains frozen:
  - no rollback of v36 `V31-F` governance release behavior in this arc.
- Closeout observability continuity lock is frozen:
  - v37 closeout must include a runtime-observability comparison row against v36 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `K1` proposer idempotency persistence boundary release (`V31-G`)
2. `K2` persistence-release determinism/regression guard suite (`V31-G`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- any additional worker-route governance behavior expansion beyond v36 baseline,
- any provider or proposer endpoint expansion,
- repo-root consolidation path (`V31-D`) beyond continuity maintenance,
- worker CLI safety path (`V31-E`) beyond continuity maintenance,
- formal-lane evidence path (`V31-C`) beyond continuity maintenance,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v37)

- v38+ policy-operations hardening may evaluate deterministic hot-reload/versioned capability-policy refresh with explicit hash/version guards and fail-closed fallback semantics.
- v38+ governance policy-shaping may introduce a distinct worker-cancel action identifier only via explicit lock update if policy needs to diverge from shared `urm.agent.cancel` behavior.
- v38+ persistence-operations hardening may introduce deterministic idempotency-record retention/TTL policy with explicit eviction-window lock text and replay safety guarantees.

## V35 Readiness Consumption (Machine-Checkable)

```json
{
  "schema": "l2_boundary_release_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md",
  "source_assertion_schema": "l2_boundary_readiness_assertion@1",
  "target": "V31-G",
  "authorized_surfaces": [
    "apps/api/src/adeu_api/main.py#_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY",
    "apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint",
    "apps/api/src/adeu_api/storage.py#transaction"
  ],
  "required_blockers": [
    "BOUNDARY_LOCK_APPROVED",
    "PERSISTENCE_SOURCE_OF_TRUTH_FROZEN",
    "REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN"
  ]
}
```

Consumption lock:

- `l2_boundary_release_consumption@1` values for `authorized_surfaces` and `required_blockers` must be exact-set matches to the authoritative v35 `target = "V31-G"` readiness assertion block.
- set-equality comparison is order-insensitive with deterministic canonicalization (lexicographic sort before compare).
- duplicate values in `authorized_surfaces` or `required_blockers` are invalid and fail closed.
- consumption assertion validation remains merge-blocking and is enforced by deterministic docs/test guards in this arc.
- `CoreIRProposerRequest.idempotency_payload` is consumed as frozen dependency for v37 hash-authority continuity and must not be modified in this arc without explicit lock update.

## V31-G Persistence Source-of-Truth Assertion (Machine-Checkable)

```json
{
  "schema": "v31g_persistence_source_of_truth_assertion@1",
  "runtime_module_path": "apps/api/src/adeu_api/main.py",
  "runtime_surface_symbol": "urm_core_ir_propose_endpoint",
  "deferred_cache_symbol": "_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY",
  "storage_module_path": "apps/api/src/adeu_api/storage.py",
  "storage_entrypoint_symbol": "transaction",
  "source_of_truth": "persisted_store_only",
  "dual_write_allowed": false
}
```

## V31-G Persisted Idempotency Record Contract (Machine-Checkable)

```json
{
  "schema": "v31g_idempotency_record_contract@1",
  "idempotency_key": "client_request_id",
  "uniqueness_constraint": "unique(client_request_id)",
  "required_fields": [
    "client_request_id",
    "provider",
    "request_payload_hash",
    "response_payload",
    "created_at"
  ],
  "determinism_authority_fields": [
    "client_request_id",
    "provider",
    "request_payload_hash",
    "response_payload"
  ],
  "nondeterministic_metadata_fields_excluded": [
    "created_at"
  ]
}
```

## V31-G Idempotency Hash Projection Assertion (Machine-Checkable)

```json
{
  "schema": "v31g_idempotency_hash_projection_assertion@1",
  "builder_symbol": "CoreIRProposerRequest.idempotency_payload",
  "hash_function": "sha256_canonical_json",
  "canonicalization_profile": "frozen_canonical_json_v1",
  "projection_mode": "closed_world",
  "additional_fields_forbidden": true,
  "included_fields": [
    "provider",
    "source_text_hash",
    "surface_id"
  ],
  "excluded_fields": [
    "client_request_id",
    "source_text"
  ]
}
```

## K1) Proposer Idempotency Persistence Boundary Release (`V31-G`)

### Goal

Release persisted single-source idempotency authority for proposer flow (`/urm/core-ir/propose`) with deterministic replay/conflict behavior.

Lock-class rationale:

- this slice is `L2` because it activates persistence boundary authority on an existing runtime endpoint.

### Scope

- Replace process-local proposer idempotency authority on:
  - `apps/api/src/adeu_api/main.py`:
    - `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`
    - `POST /urm/core-ir/propose` (`urm_core_ir_propose_endpoint`)
- Persist proposer idempotency records using:
  - `apps/api/src/adeu_api/storage.py#transaction`
  - deterministic canonical payload-hash comparison from `CoreIRProposerRequest.idempotency_payload` and `sha256_canonical_json`.
- Freeze hash semantic projection for proposer idempotency:
  - semantic hash projection is exactly `surface_id`, `provider`, `source_text_hash`,
  - no additional semantics-bearing fields are allowed for `/urm/core-ir/propose` idempotency decisions in this arc.
- Freeze persisted idempotency write model:
  - persist-after-success-only; partial/in-progress durable rows are forbidden for this arc,
  - replay authority requires persisted `response_payload` on every committed idempotency row,
  - persisted idempotency commit must occur before handler success return.
- Freeze deterministic race handling under uniqueness:
  - persisted write path uses a unique constraint on `client_request_id` in a proposer-specific persisted table,
  - on unique-constraint collision, runtime must read stored row and deterministically branch:
    - (`provider`, `request_payload_hash`) both match -> replay stored `response_payload`,
    - (`provider`, `request_payload_hash`) mismatch -> fail closed with existing proposer request-invalid code path.
- Freeze replay payload serialization authority:
  - replay response serialization must use frozen canonical JSON profile authority for deterministic output.
- Preserve existing proposer endpoint response contract:
  - `CoreIRProposerResponse`.
- Preserve existing provider boundary:
  - `provider = "codex"` only.
- Preserve structured conflict/invalid semantics for reused `client_request_id`:
  - same semantic payload -> deterministic replay response,
  - different provider or different semantic payload -> deterministic structured conflict/invalid error detail.

### Locks

- Persistence authority lock is frozen:
  - proposer idempotency source of truth for this release is persisted store only.
- Persisted record-model lock is frozen:
  - persisted idempotency record contract is fixed to `v31g_idempotency_record_contract@1`,
  - required stored fields are exactly `client_request_id`, `provider`, `request_payload_hash`, `response_payload`, `created_at`.
- Uniqueness lock is frozen:
  - persisted idempotency uniqueness authority is `unique(client_request_id)`,
  - existing runtime tuple key semantics (`surface_id`, `client_request_id`) are equivalent in proposer path because `surface_id` is constant (`adeu_core_ir.propose`) for this endpoint family,
  - proposer idempotency persisted table in v37 is propose-specific and must not be reused for other surfaces without explicit future lock update.
- No-dual-source lock is frozen:
  - process-local `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` may not remain authoritative once v37 release is active,
  - dual-read/dual-write operation is forbidden unless a future lock explicitly defines migration semantics,
  - in-memory `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` may remain only as non-authoritative performance cache and must never change replay/conflict outcomes,
  - cache lookup/write usage in proposer authoritative decision path is forbidden in this arc.
- Endpoint contract continuity lock is frozen:
  - `CoreIRProposerResponse` schema and success payload shape remain compatible.
- Canonical hash-projection lock is frozen:
  - replay/conflict hash authority is `CoreIRProposerRequest.idempotency_payload` with exact included fields (`surface_id`, `provider`, `source_text_hash`) and excluded fields (`client_request_id`, raw `source_text`),
  - hash projection is closed-world: additional top-level fields are forbidden before canonical hash evaluation,
  - hash function and canonicalization profile remain `sha256_canonical_json` under frozen canonical JSON rules.
- Deterministic replay/conflict lock is frozen:
  - replay/conflict decisions remain keyed by deterministic canonical hash of proposer idempotency payload plus persisted uniqueness on `client_request_id`,
  - replay/conflict comparison key is exactly tuple (`provider`, `request_payload_hash`) on the persisted row,
  - replay/conflict branches remain machine-assertable on structured fields (`code`, `context.client_request_id`, `context.provider` where present),
  - prose `reason`/message fields are non-authoritative for determinism assertions.
- Crash/incomplete-state lock is frozen:
  - durable idempotency rows are written only after successful response payload construction,
  - if process crash/termination occurs before durable commit, request is treated as not-yet-persisted on retry and must be re-evaluated under the same deterministic rules,
  - partially persisted/in-progress durable rows are forbidden in this arc.
- Race-resolution lock is frozen:
  - unique-constraint collisions on `client_request_id` must not produce ambiguous outcomes,
  - collision resolution must reuse existing proposer request-invalid code path (`_CORE_IR_PROPOSER_REQUEST_INVALID_CODE`) for mismatch branches and deterministic replay for hash-match branches,
  - missing/invalid required stored fields on collision reconciliation path fail closed on existing proposer payload-invalid code path (`_CORE_IR_PROPOSER_PAYLOAD_INVALID_CODE`).
- Error-code continuity lock is frozen:
  - no new URM error-code family is introduced by this release,
  - existing proposer invalid/payload/provider error code paths remain authoritative,
  - proposer replay/conflict mismatch branches remain on existing `_CORE_IR_PROPOSER_REQUEST_INVALID_CODE` path; `URM_IDEMPOTENCY_KEY_CONFLICT` introduction/use is out-of-scope for this arc.
- Conflict-context determinism lock is frozen:
  - proposer mismatch branches on `_CORE_IR_PROPOSER_REQUEST_INVALID_CODE` must include deterministic structured context fields:
    - `context.client_request_id`
    - `context.provider_expected`
    - `context.provider_observed`
    - `context.request_payload_hash_expected`
    - `context.request_payload_hash_observed`
- Persisted-provider field lock is frozen:
  - persisted idempotency `provider` field for this arc must be exactly `codex`; invalid provider values fail closed on existing proposer request-invalid code path.
- Governance continuity lock is frozen:
  - v37 may not modify v36 worker governance release behavior (`/urm/worker/run`, `/urm/worker/{worker_id}/cancel` policy gating).
- Replay/no-mutation continuity lock is frozen:
  - release may not introduce nondeterministic response fields on proposer replay/conflict envelopes.

### Acceptance

- `/urm/core-ir/propose` idempotency authority is persisted-store-backed and deterministic.
- Same idempotency key + same semantic payload yields deterministic replay behavior.
- Same idempotency key + different semantic payload/provider fails closed with deterministic structured error detail.
- No rollback/regression of v36 `V31-F` governance behavior is introduced.

## K2) Persistence-Release Determinism/Regression Guards (`V31-G`)

### Goal

Prove the `V31-G` boundary release is deterministic, fail-closed, and regression-resistant while preserving v36 governance continuity.

### Scope

- Add/adjust deterministic tests/guards for:
  - proposer endpoint persisted-idempotency callgraph coverage through `storage.transaction`,
  - HTTP-path proof for persisted idempotency behavior via API test client over real route/dependency wiring,
  - deterministic parsing/validation of `l2_boundary_release_consumption@1` for `target = "V31-G"` with exact-set membership checks,
  - deterministic replay assertions for same `client_request_id` + same payload hash,
  - deterministic conflict assertions for same `client_request_id` + different semantic payload hash,
  - deterministic provider-mismatch assertions for same `client_request_id` + different provider,
  - source-of-truth assertions:
    - replay behavior remains correct even when process-local in-memory cache is absent/reset,
    - persisted store remains authoritative for replay/conflict decisions,
    - replay/conflict behavior remains deterministic after process restart (fresh app instance) for persisted entries,
    - cache-present execution never returns replay/conflict result for an entry absent in persisted store,
  - deterministic allowed-path contract compatibility for `CoreIRProposerResponse`,
  - anti-regression checks that v37 release does not alter v36 `V31-F` governance routing behavior.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v37 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v36 continuity metrics remain at required values.
- Guard entrypoint lock is frozen:
  - boundary-consumption and persistence-release lint entrypoint is `apps/api/scripts/lint_v31g_persistence_release.py`,
  - frozen v37 persistence lint CLI is:
    - `TZ=UTC LC_ALL=C PYTHONPATH=apps/api/src:packages/urm_runtime/src .venv/bin/python apps/api/scripts/lint_v31g_persistence_release.py --lock-doc docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md --base-ref origin/main`,
  - merge-base diff semantics for lint are frozen:
    - branch-owned changes are computed with merge-base against `--base-ref`,
    - raw two-dot tip-to-tip diff is forbidden,
  - detached/archive mode contract is frozen:
    - unresolved git metadata or unresolvable `--base-ref` fails closed with exit code `5`,
  - frozen v37 persistence lint exit-code contract is:
    - `0` = pass
    - `2` = assertion schema/ordering/membership violation
    - `3` = persisted-idempotency callgraph/source-of-truth violation
    - `4` = replay/conflict determinism drift
    - `5` = base-ref unavailable/unresolvable for merge-base diff guard
- Required-persistence-callgraph lock is frozen:
  - v37 guards fail closed if proposer idempotency replay/conflict branches do not pass through persisted-store authority path.
- HTTP-path evidence lock is frozen:
  - release evidence for persisted replay/conflict behavior must come from test-client-driven request paths through mounted route/dependency wiring,
  - pure unit-level direct handler invocation is insufficient as merge-blocking evidence.
- Deterministic replay/conflict assertion lock is frozen:
  - v37 guards assert structured replay/conflict fields and may not depend on prose matching.
- In-memory-authority regression lock is frozen:
  - v37 guards fail closed if clearing/resetting process-local cache changes replay/conflict outcomes for persisted entries.
- Cache non-authoritative presence lock is frozen:
  - v37 guards fail closed if cache-present runs return idempotency outcomes not backed by persisted-store entries.
- Process-restart continuity lock is frozen:
  - v37 guards fail closed if replay/conflict outcomes for persisted entries change after fresh process/app restart.
- Governance continuity lock is frozen:
  - v37 guards fail closed if v36 worker governance gating regresses (`authorize_action` required on worker run/cancel paths remains true).
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- No-provider/no-network expansion lock is frozen:
  - no new provider types beyond existing `codex` are allowed for proposer persistence release in this arc,
  - tests run with deterministic mocking and may not require outbound network.
- CI lane continuity lock is frozen:
  - in-scope v37 persistence guards must run in the default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required persisted-idempotency callgraph assertions are green for `/urm/core-ir/propose`.
- Replay/conflict behavior remains deterministic and machine-assertable.
- Replay/conflict behavior for persisted entries remains deterministic across process restarts.
- `CoreIRProposerResponse` allowed-path contract remains compatible.
- v36 worker-governance continuity guards remain green under v37 scope.

## Stop-Gate Impact (v37)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v37 closeout must include runtime-observability comparison row against v36 baseline.
- Runtime-observability comparison schema lock is frozen:
  - comparison block schema is docs-only `runtime_observability_comparison@1`,
  - required keys are:
    - `schema`
    - `baseline_arc`
    - `current_arc`
    - `baseline_source`
    - `current_source`
    - `baseline_elapsed_ms`
    - `current_elapsed_ms`
    - `delta_ms`
    - `notes`
  - optional keys may be included for richer continuity evidence (`baseline_total_fixtures`, `current_total_fixtures`, `baseline_total_replays`, `current_total_replays`, `baseline_bytes_hashed_per_replay`, `current_bytes_hashed_per_replay`, `baseline_bytes_hashed_total`, `current_bytes_hashed_total`) but are non-required for v37 closeout compatibility with frozen v36 baseline artifacts.
- Runtime-observability closeout placement lock is frozen:
  - v37 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md` inside a machine-checkable JSON block.

## Error/Exit Policy (v37)

- No new URM error-code family is introduced in this arc.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `runtime/api: release V31-G proposer idempotency persistence boundary`
2. `tests: add v37 persistence-release determinism and regression guard suite`

## Intermediate Preconditions (for v37 start)

1. v36 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v36 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS36.md`
3. In-scope persistence authority surfaces remain available at v37 start:
   - `apps/api/src/adeu_api/main.py`
   - `apps/api/src/adeu_api/storage.py`
4. Frozen v36 governance release baseline remains true at v37 start:
   - `/urm/worker/run` and `/urm/worker/{worker_id}/cancel` are policy-gated through `authorize_action`.
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. Existing boundary-readiness lint remains enabled:
   - `apps/api/scripts/lint_l2_boundary_readiness.py`
7. Persistence-release lint entrypoint path is reserved for this arc and introduced by `K2`:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
8. Existing proposer endpoint baseline remains true at v37 start:
   - `apps/api/src/adeu_api/main.py#urm_core_ir_propose_endpoint` currently reads/writes process-local `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY`.
9. No additional `L2` boundary release beyond `V31-G` is introduced in this arc.

## Exit Criteria (Draft)

- `K1` and `K2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic proposer-idempotency persistence release (`V31-G`) is closed and test-covered.
- v37 closeout evidence includes runtime-observability comparison row against v36 baseline.
- v36 governance boundary release continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
