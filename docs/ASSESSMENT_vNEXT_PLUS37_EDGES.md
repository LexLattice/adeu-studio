# Assessment vNext+37 Edges (K1 + K2 Planning)

This document records pre-implementation edge analysis for `vNext+37` (`V31-G` persistence boundary release), aligned to `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md`.

Status: planning assessment (lock drafted, implementation not started).

## Scope

- In scope: `K1` proposer idempotency persistence release and `K2` deterministic guard/lint suite.
- Out of scope: runtime semantics changes, additional `L2` releases, provider/proposer expansion.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS36.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `apps/api/src/adeu_api/main.py`
- `apps/api/src/adeu_api/storage.py`

## Repository Baseline Anchors

1. Proposer idempotency is currently process-local:
   - `_CoreIRProposerIdempotencyRecord` + `_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY` in `apps/api/src/adeu_api/main.py:582` and `apps/api/src/adeu_api/main.py:588`.
2. Proposer endpoint currently uses in-memory cache path:
   - `/urm/core-ir/propose` at `apps/api/src/adeu_api/main.py:7347`.
   - hash generation at `apps/api/src/adeu_api/main.py:7350`.
   - cache read/write at `apps/api/src/adeu_api/main.py:7351` and `apps/api/src/adeu_api/main.py:7432`.
3. Error-code anchors already exist and are reusable:
   - `_CORE_IR_PROPOSER_REQUEST_INVALID_CODE` at `apps/api/src/adeu_api/main.py:450`.
   - `_CORE_IR_PROPOSER_PAYLOAD_INVALID_CODE` at `apps/api/src/adeu_api/main.py:452`.
   - legacy `_IDEMPOTENCY_CONFLICT_CODE` exists at `apps/api/src/adeu_api/main.py:388` but is not proposer authority.
4. Persisted transaction entrypoint exists:
   - `transaction()` in `apps/api/src/adeu_api/storage.py:160`.
5. No proposer-specific idempotency persisted table exists yet in `storage.py`.

## K1 Edge Set (Persistence Release)

1. Persisted record contract gap:
   - v37 requires persisted fields `client_request_id`, `provider`, `request_payload_hash`, `response_payload`, `created_at`; current runtime record has only `provider`, `request_payload_hash`, `response_payload`.
2. Uniqueness semantics:
   - current in-memory key is tuple (`surface_id`, `client_request_id`); v37 persists `unique(client_request_id)` in propose-specific table.
3. Hash authority lock:
   - `CoreIRProposerRequest.idempotency_payload` in `apps/api/src/adeu_api/main.py:879` must remain frozen as dependency for v37.
4. Closed-world projection:
   - hash projection must remain exactly (`surface_id`, `provider`, `source_text_hash`) with no extra semantics-bearing fields.
5. Collision transaction integrity:
   - uniqueness collisions must not perform reconciliation reads on aborted transactions; implementation must use conflict-safe write primitive or rollback+fresh transaction path.
6. Persist-after-success-only:
   - no durable partial/in-progress rows; commit must happen before success return.
7. Replay payload authority:
   - deterministic replay requires persisted `response_payload` and deterministic serialization authority.
8. Conflict branch precedence:
   - comparison key is (`provider`, `request_payload_hash`); both must match for replay.
9. Conflict context determinism:
   - mismatch path must emit deterministic context fields (`client_request_id`, provider expected/observed, hash expected/observed).
10. Cache non-authoritative posture:
    - in-memory cache may exist as optimization only; authoritative decision path must be persisted-store-backed.

## K2 Edge Set (Guard/Lint Suite)

1. New lint entrypoint is required:
   - `apps/api/scripts/lint_v31g_persistence_release.py` is not present yet and must be introduced by `K2`.
2. Merge-base semantics:
   - guard diff logic must use merge-base with `--base-ref`, not raw two-dot tip diff.
3. Detached/archive fail-closed behavior:
   - unresolved git metadata or base ref must exit deterministically with code `5`.
4. Restart determinism:
   - tests must prove replay/conflict outcomes remain stable across fresh app/process restart.
5. Cache reset and cache-present invariants:
   - clearing cache must not change outcomes.
   - cache-present execution must not return outcomes absent in persisted store.
6. HTTP-path evidence requirement:
   - merge-blocking evidence must come from test-client request paths, not direct handler-only unit calls.
7. Governance continuity coverage:
   - v36 `V31-F` assertions must stay green while v37 changes land.

## Implementation Readiness Notes

1. v37 lock is sufficiently precise to begin `K1`, with explicit constraints for persistence, collision behavior, and deterministic replay.
2. Highest execution risk is collision transaction handling under uniqueness and restart-determinism coverage in `K2`.
3. Recommended order:
   - `K1`: persisted proposer idempotency table + runtime wiring + deterministic branch context.
   - `K2`: lint/guard entrypoint + restart/cache invariants + merge-base/detached fail-closed behavior.

## Next Actions

1. Start `K1` on a fresh branch with small green runtime/api PR.
2. Add `K2` guard suite in follow-on tests/docs PR, including lint entrypoint and exit-code contract.
3. Keep v36 governance continuity tests mandatory in both PRs.
