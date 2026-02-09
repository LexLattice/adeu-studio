# Locked Roadmap vNext+2 (Frozen)

This document freezes the next roadmap after `vNext+1` as lockable implementation work:

`M8.1 -> M9 -> M10 -> M11`

The intent is zero taxonomy drift and zero contract ambiguity.

## Existing Enum References (Code-Source Freeze)

Use current labels exactly unless a future milestone explicitly versions a new label set.

- `solver_trust`:
  - `kernel_only | solver_backed | proof_checked`
  - source: `apps/api/src/adeu_api/main.py` (`SolverTrustLevel`)
- `proof_trust`:
  - `lean_core_v1_proved | lean_core_v1_partial_or_failed | mock_backend_not_proof_checked | no_required_proofs | null`
  - source: `apps/api/src/adeu_api/main.py` (`ArtifactProofTrust` + nullable fields)
- `mapping_trust` (current emitted values):
  - `derived_bridge | derived_alignment | null`
  - source: `apps/api/src/adeu_api/main.py` (`/adeu/analyze_concepts`, `/concepts/align`, `/concepts/questions`)
  - `vNext+2` lock: promote to shared typed alias in API code:
    - `MappingTrustLevel = Literal["derived_bridge", "derived_alignment"]`
    - response fields use `MappingTrustLevel | null`

Canonical hashing/serialization utilities must be reused:

- `apps/api/src/adeu_api/hashing.py`
  - `canonical_json`
  - `sha256_text`
  - `sha256_canonical_json`

## Cross-Milestone Global Locks

- No solver semantic changes. Only orchestration, ranking, evidence packaging, and UX.
- All API additions are additive unless explicitly marked breaking (none in this plan).
- Trust lanes remain explicit on all new/modified responses:
  - `mapping_trust`
  - `solver_trust`
  - `proof_trust`
- Determinism contract:
  - stable sort key and tie-breaks for every list output
  - permutation invariance tests required where applicable
- IDs must be hash-derived from canonical payloads, never index-based.
- New labels/enums are forbidden unless versioned and added with tests + docs in the same PR.

## Endpoint Side-Effect Policy (Frozen)

- `POST /concepts/questions`: read-only, no persistence, no side effects.
- `POST /adeu/questions` (new): read-only, no persistence, no side effects.
- `POST /concepts/apply_patch`: mutating/evaluative flow, stale-IR guard required.
- `POST /concepts/apply_ambiguity_option`: mutating/evaluative flow, stale-IR guard required.
- `POST /concepts/tournament` (new): advisory only, no persistence by default.
- read-only endpoints may still accept stale-state preconditions (`expected_ir_hash`) and return `409` on mismatch.

Behavior change lock:

- Current code may persist validator runs for `/concepts/questions` behind env flags.
- In `vNext+2`, questions endpoints are explicitly read-only and must ignore persistence flags.

## Shared Eval and Metrics Locks

### Fixture Set (Frozen)

Only these contribute to quality metrics:

- `examples/eval/questions/**`
- `examples/eval/tournament/**`

Excluded:

- ad-hoc fixtures outside `examples/eval/**`

### Quality Dashboard Artifact (CI-Emitted)

- `question_stability_pct`
- `avg_questions_per_ir`
- `avg_resolved_per_session`
- `avg_solver_calls_per_action`
- `p95_latency_ms` (per endpoint/action)

CI policy lock:

- Blocking gates: determinism, invariance, and budget adherence.
- Latency is report-only initially (non-blocking) to avoid runner variance noise.

## Error Code Registry (Frozen)

Schema-validation status lock:

- no global FastAPI request-validation remapping is assumed in `vNext+2`
- request shape validation errors remain `422`

### `/concepts/questions`

- `QUESTIONS_SCHEMA_INVALID` (422)
- `QUESTIONS_ANCHOR_MISSING` (400)
- `QUESTIONS_STALE_IR_HASH_MISMATCH` (409)
- `QUESTIONS_INTERNAL_ERROR` (500, fallback only)

### `/adeu/questions`

- `ADEU_QUESTIONS_SCHEMA_INVALID` (422)
- `ADEU_QUESTIONS_BRIDGE_FAILED` (400)
- `ADEU_QUESTIONS_ANCHOR_UNRESOLVED` (400)
- `ADEU_QUESTIONS_STALE_IR_HASH_MISMATCH` (409)

### Tournament

- `TOURNAMENT_SCHEMA_INVALID` (422)
- `TOURNAMENT_STALE_IR_HASH_MISMATCH` (409)
- `TOURNAMENT_NO_CANDIDATES` (400)
- `TOURNAMENT_PROVIDER_ERROR` (502)

### Document

- `DOC_TEXT_MISMATCH` (400)
- `DOC_NOT_FOUND` (404)

Compatibility lock:

- Existing `STALE_IR` responses stay supported as alias during transition.
- New endpoint-specific stale codes may be introduced, but clients must still handle `STALE_IR`.
- Budget exhaustion is not a top-level error code for questions/tournament; it is represented in `budget_report`.

## ID Recipe Locks (Hash-Based)

### `question_id`

`sha256(canonical_json({ endpoint_kind, signal_kind, anchors, option_ids, question_rank_version }))[:12]`

### `resolved_key`

`sha256(canonical_json({ signal_kind, anchors_sorted, selected_option_id }))[:12]`

### `candidate_id` (tournament)

`sha256(canonical_json({ base_ir_hash, patch_ops_canonical, question_id, tournament_score_version }))[:12]`

Invariant:

- no index-derived IDs
- no timestamp/DB primary key inputs in these IDs

## Stale-State Guard Lock

Any patch-apply or patch-generating mutation path requires an IR precondition:

- request includes `expected_ir_hash`
- server computes current hash from canonical IR JSON
- mismatch returns `409` with stale code (`*_STALE_IR_HASH_MISMATCH` and/or `STALE_IR` alias)

Applies to:

- `/concepts/apply_patch`
- `/concepts/apply_ambiguity_option`
- tournament apply/generate paths when they act on mutable IR state
- read-only endpoints (`/concepts/questions`, `/adeu/questions`) when `expected_ir_hash` is supplied as a client safety precondition

## Budget Report Schema (Frozen)

Questions and tournament responses include:

- `budget_version: "budget.v1"`
- `max_solver_calls: int`
- `used_solver_calls: int`
- `max_dry_runs: int`
- `used_dry_runs: int`
- `truncated: bool`
- `truncation_reason: "solver_call_cap_reached" | "dry_run_cap_reached" | "max_questions_reached" | "candidate_cap_reached" | null`

Availability lock:

- `budget_report` is always present for predictable client behavior.
- Budget exhaustion is represented as `200` with `truncated=true` and reason metadata.
- No `warnings[]` budget envelope is introduced in `vNext+2`.

## Anchor Contract (Frozen)

Shared anchor shape lock (`AnchorRef`, reused across concepts/legal/tournament outputs):

- `object_id: str | null`
- `json_path: str | null`
- `label: str | null`
- `span: { start: int, end: int } | null`
- canonical anchor sort key for hashing/ranking:
  - `(object_id or "", json_path or "", label or "", span.start or -1, span.end or -1)`

- If `source_text` is absent:
  - anchors must include `object_id` + `json_path`
  - `span` must be `null`
- If `source_text` is present:
  - `span` is optional
  - if present, it must be bounds-checked
- Spans must never be fabricated from heuristics.

## Pagination Determinism Lock (M10 Lists)

- Default sort: `created_at DESC`, tie-break `id ASC`.
- Pagination contract: `limit/offset`.
- Insert behavior lock:
  - offset pagination is best-effort; inserts between pages may shift subsequent pages.
  - this is documented and tested as contract, not treated as bug.

## Milestone M8.1: Question Quality v2 (Calibration + Determinism Hardening)

Goal: harden existing questions flow for signal quality and deterministic behavior.

### M8.1 Locks

`/concepts/questions` request schema (frozen, strict `extra="forbid"`):

- `ir: ConceptIR`
- `source_text?: str`
- `doc_id?: str`
- `mode: STRICT|LAX = LAX`
- `include_forced_details: bool = false`
- `expected_ir_hash?: str`
- no `include_validator_runs` field in M8.1 (explicit non-goal)

`/concepts/questions` response schema (frozen, additive):

- existing fields:
  - `check_report`
  - `questions[]`
  - `question_count`
  - `max_questions`
  - `max_answers_per_question`
  - trust lanes (`mapping_trust`, `solver_trust`, `proof_trust`)
- additive fields:
  - `question_rank_version: "concepts.qrank.v2"`
  - `budget_report`

- Add `question_rank_version` metadata:
  - `/concepts/questions`: `concepts.qrank.v2`
- Freeze resolved equivalence semantics:
  - based on `resolved_key` hash recipe above, not raw runtime IDs
- Do-no-harm remains dry-run based with strict caps and deterministic truncation.
- Questions endpoint is read-only (no persistence, no side effects).

### M8.1 Success Metrics

- Stability: 100% identical question ordering over 20 repeated runs (same IR/mode).
- Permutation invariance: 100% for permuted claims/links/ambiguities ordering.
- Budget adherence: 100% (never exceeds declared caps).

### M8.1 Acceptance

- same input -> identical `questions[]` and ordering
- permuted input lists -> identical `questions[]`
- exhausted budget -> deterministic `truncated=true` + stable `budget_report`

### M8.1 Rollout

- API first
- minimal UI update only for version/truncation display

## Milestone M9: Legal-native Socratic Layer (`POST /adeu/questions`)

Goal: legal span-anchored questions powered by deterministic ADEU -> Concepts bridging.

### M9 API Contract (Frozen, Additive)

Request:

- `ir: AdeuIR`
- `source_text?: str`
- `mode: STRICT|LAX = LAX`
- `include_validator_runs: bool = false`
- `include_analysis_details: bool = false`
- `expected_ir_hash?: str`

Response:

- `questions[]`
- `question_rank_version: "adeu.qrank.v1"`
- `bridge_manifest`
- `bridge_mapping_version`
- `mapping_hash`
- trust lanes: `mapping_trust`, `solver_trust`, `proof_trust`
- `budget_report`

### M9 Locks

- determinism: same ADEU IR -> same bridge output and question ordering
- `mapping_trust` for this endpoint uses existing bridge lane label: `derived_bridge`
- anchors must resolve to ADEU `object_id/json_path` (and validated span if source text present)
- advisory only; no auto-apply
- read-only; no persistence side effects

### M9 Success Metrics

- anchor validity: 100% on eval fixtures
- stability: 100% over 20 repeated runs

### M9 Acceptance

- deterministic bridge hash + ordering under input permutations
- question anchor -> legal span highlight round-trip works deterministically

### M9 Rollout

- API first
- then reuse questions UI component on legal page

## Milestone M10: Paper Abstract Studio v0

Goal: documents-first paper workflow with existing primitives.

### M10 Locks

- prefer existing APIs:
  - `/documents/*`
  - `/concepts/*`
  - `/concepts/align`
- precedence:
  - if `doc_id` and `source_text` both provided, `doc_id` authoritative
  - mismatch returns `DOC_TEXT_MISMATCH`
- document immutability preserved
- list/pagination determinism rules above are mandatory

### M10 Success Metrics

- end-to-end path on fixtures:
  - create document (`domain="paper.abstract"`)
  - concepts propose/check/analyze
  - accept concept artifact
  - align across docs
- align ordering invariant under doc-order permutations

### M10 Acceptance

- deterministic document listing/filtering
- reproducible provenance across sessions for same `doc_id`

### M10 Rollout

- UI first with minimal backend additions

## Milestone M11: Repair Tournament (Typed, Evidence-scored, Advisory)

Goal: rank patch candidates with deterministic scoring and strict budgeting.

### M11 Mode Lock

Two explicit modes:

- `live_generation`:
  - provider-generated candidates; candidate set may vary
  - ranking determinism required for a fixed candidate set
- `replay_candidates`:
  - candidates provided in request
  - full deterministic ranking/evidence required
  - used for CI goldens

### M11 Contract Locks

- `tournament_score_version: "concepts.tscore.v1"`
- advisory only: never auto-commit
- shared server-side apply core only (no client patch semantics)
- strict per-request solver/dry-run budgets + deterministic truncation
- stale-IR guard required for apply/generate paths
- replay guardrails:
  - bounded candidate count
  - bounded total patch ops
  - bounded payload bytes
  - deterministic rejection codes

### M11 Success Metrics

- deterministic ranking in replay mode (same inputs -> same outputs)
- top candidate must strictly improve objective vector or return explicit `no_safe_improvement`
- 100% budget adherence

### M11 Acceptance

- golden replay fixtures for:
  - chooses better patch
  - no safe improvement
- top-K include complete evidence bundles

### M11 Rollout

- API first (headless)
- UI second (run tournament action from selected question)

## Implementation Sequence (Frozen)

1. M8.1
2. M9
3. M10
4. M11
