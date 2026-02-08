# Locked Roadmap vNext+1 (Frozen)

This document captures the post-A->D continuation locks and implementation order.

`E0 -> E2 -> E1 -> F -> G` (then `H` as a later large milestone)

## Cross-Milestone Locks

- Trust metadata remains additive and lane-separated on new/modified endpoints:
  - `mapping_trust`
  - `solver_trust`
  - `proof_trust`
- Do not change solver semantics.
- Do not break existing API contracts unless explicitly called out in a milestone lock.

## Milestone E0: Concept Accept Atomicity Parity

Goal: concepts artifacts are as trustworthy as legal artifacts.

### E0.1) Persistence Policy (Locked)

- `POST /concepts/artifacts` always persists validator runs on accept (parity with legal).
- Environment flags may still control non-accept transient endpoints, but accept ignores them.

### E0.2) Transaction Scope (Locked)

Single SQLite transaction includes all:

- concept artifact row
- validator_runs rows
- analysis snapshot (`analysis_json`)
- derived metadata columns written on accept (status counts, hashes)

Ordering lock:

- run `ensure_schema/migrations` before `BEGIN IMMEDIATE`.

### E0.3) Failure Injection Test (Locked)

- Inject a failure in validator run persistence after artifact insert.
- Expected invariant: zero new rows across:
  - `concept_artifacts`
  - `validator_runs`
  - any related accept-path tables

## Milestone E2: Unified Patch-Apply Surface

Goal: one deterministic patch gateway with no duplicated semantics.

### E2.1) Response Contract Reuse (Locked)

- `POST /concepts/apply_patch` returns the same shape as `/concepts/apply_ambiguity_option`:
  - `patched_ir`
  - `check_report`
  - optional `validator_runs` behind `include_validator_runs`
  - trust metadata fields

### E2.2) Error Contract (Locked)

- Error shape is shared across both endpoints:
  - `errors: [{ op_index, path, code, message }]`
  - sorted by `(op_index, path, code)`
- Code enum reuse only (no ad-hoc strings):
  - `PATCH_INVALID_OP`
  - `PATCH_PATH_FORBIDDEN`
  - `PATCH_TEST_FAILED`
  - `PATCH_APPLY_FAILED`
  - `PATCH_REF_INTEGRITY_VIOLATION`
  - `PATCH_SIZE_LIMIT`

### E2.3) Trust Metadata (Locked)

- `/concepts/apply_patch` response includes:
  - `mapping_trust` (typically `none` for local patch apply)
  - `solver_trust` (kernel-only or solver-backed, per run evidence)
  - `proof_trust` (typically `none`)

### E2.4) Wrapper Parity (Locked)

- `/concepts/apply_ambiguity_option` becomes a thin wrapper:
  - resolve `option_id -> AmbiguityOption.patch`
  - call shared internal `apply_patch_core(...)`
  - same validation, sorting, and error semantics

## Milestone E1: Questions Loop UX

Goal: make `/concepts/questions` part of normal daily workflow.

### E1.1) Resolved Semantics (Locked)

Because `question_id` may churn after re-analyze, UI resolves by deterministic equivalence key:

- `(signal_kind, anchor_object_ids, anchor_json_paths, selected_answer_option_id)`

Not by raw `question_id`.

### E1.2) Stale-IR Guard (Locked)

- Apply requests include `ir_hash` (`sha256` of canonical IR JSON).
- Server recomputes and rejects with `409 STALE_IR` on mismatch.
- Client refreshes IR and retries.

## Milestone F: Question Quality Engine

Goal: fewer, higher-impact, deterministic questions.

### F.1) Ranking Key Freeze (Locked)

Lexicographic tuple (deterministic):

1. `priority_class` (lower is better): `0=UNSAT_MIC`, `1=FORCED_EDGE`, `2=DISCONNECT`, `3=OTHER`
2. `impact_score` (higher is better):
   - MIC: `len(mic_atoms)`
   - forced: `1` (or affected-edge count if available)
   - disconnect: size of smaller component (or term count)
3. `severity_rank` (lower is better)
4. `anchor_key` (stable join of sorted `(object_id,json_path)`)
5. `template_id`
6. `question_text` (final tie-break)

### F.2) Do-No-Harm Budget (Locked)

- Do-no-harm uses `dry_run=true` + deterministic check/analyze.
- Caps:
  - `max_dry_run_evals_total = 20` per request
  - `max_solver_calls_total = 40` per request
- Evaluate candidates in rank order until budget exhaustion.

## Milestone G: Documents Ingest + Persistent Provenance

Goal: make text persistent and provenance reusable across sessions.

### G.1) `source_text` vs `doc_id` Precedence (Locked)

- If both are present:
  - `doc_id` is authoritative
  - if `source_text != stored_source_text`, return `400 DOC_TEXT_MISMATCH`
  - no silent override

### G.2) Document Mutability (Locked)

- Documents are immutable after creation.
- Changes require a new `doc_id` (or explicit new `doc_version` row).
- Provenance spans always refer to immutable stored text.

## Milestone H: Cross-Artifact Alignment + Proof Pressure Pilot (Detailed)

Milestone H starts only after G and is split into a short H1 retrospective gate plus H2 implementation.

Global H lock:

- Keep solver semantics unchanged.
- Keep alignment suggestions advisory only (no forced merge behavior).
- Keep trust lanes additive and conservative (`proof_checked` only when strict criteria are met).

### H0) Pre-H2 H1 Retrospective Gate (Required)

Before writing H2 code, confirm H1 still satisfies these invariants on `main`:

### H0.1) Alignment Scope Contract (Locked)

- Input normalization:
  - trim all `artifact_ids` and `doc_ids`
  - drop empty tokens
- Mixed scope (`artifact_ids` + `doc_ids`) is allowed and deterministic:
  - effective scope is union of explicit artifact ids and doc-resolved artifact ids
  - dedupe by artifact id
- `doc_id -> artifact` mapping rule:
  - choose latest concept artifact by `created_at DESC`
  - tie-break by `artifact_id ASC`
- Error behavior:
  - doc has no artifacts -> `ALIGNMENT_DOC_NO_ARTIFACT`
  - explicit artifact not found -> `ALIGNMENT_ARTIFACT_NOT_FOUND`
  - effective scope empty -> `ALIGNMENT_SCOPE_EMPTY`

### H0.2) Vocabulary Key Contract (Locked)

- `vocabulary_key` is canonicalized as:
  - lowercase input
  - tokenize with regex `[a-z0-9]+`
  - join tokens with a single space
- For H1 baseline, both `merge_candidate` and `conflict_candidate` use the normalized term label key.
- Suggestion ordering remains deterministic by:
  - `kind_rank`, `vocabulary_key`, `suggestion_id`

### H0.3) Trust + Errors Stability (Locked)

- `/concepts/align` keeps explicit trust lanes:
  - `mapping_trust="derived_alignment"`
  - `solver_trust="kernel_only"`
  - `proof_trust=null`
- Stable error code set for current scope resolution:
  - `ALIGNMENT_SCOPE_EMPTY`
  - `ALIGNMENT_DOC_NO_ARTIFACT`
  - `ALIGNMENT_ARTIFACT_NOT_FOUND`

If any H0 gate fails, fix as `H1.1` before H2.

### H1) Alignment (Baseline + Optional Hardening)

Baseline scope (already merged):

- Shared vocabulary alignment suggestions across artifacts/documents.
- `merge_candidate` and `conflict_candidate` suggestion kinds.
- Stable sorting and deterministic response payload.

Optional H1.1 hardening (non-blocking unless triggered by product need):

- Add additive `suggestion_fingerprint` for client-side dedupe across refreshes.
  - recipe lock:
    - `suggestion_fingerprint = sha256(canonical_json({...}))[:12]`
    - canonical payload uses only deterministic semantic keys (`kind`, `vocabulary_key`, sorted concept/term/sense ids)
    - never include timestamps or DB primary keys
- Add deterministic large-scope guard:
  - `ALIGNMENT_SCOPE_TOO_LARGE` when expanded effective artifact scope exceeds `max_artifacts=200`
  - cap is applied after doc->artifact expansion and dedupe
- Add additive `alignment_stats` summary for quick UX rendering (counts by kind).

### H2) Proof Pilot (Narrow, Explicit Slice)

Goal: make `proof_checked` meaningful for a narrow legal slice without changing solver behavior.

### H2.1) Invariant Slice Lock

H2 trust promotion is limited to two core ADEU obligations:

- `conflict_soundness`
- `pred_closed_world`

`exception_gating` may still be recorded, but is not required for H2 trust promotion.

### H2.2) Required Obligation Identity + Row Selection (Locked)

Required obligation keys are exact `(semantics_version, obligation_kind)` pairs:

- `("adeu.lean.core.v1", "conflict_soundness")`
- `("adeu.lean.core.v1", "pred_closed_world")`

Matching rules:

- use `proof_artifacts.details_json.semantics_version`
- use `proof_artifacts.details_json.obligation_kind`
- duplicates resolve to one effective row per key:
  - latest by `created_at DESC`
  - tie-break by `proof_id DESC`

### H2.3) Proof Timing Model (Locked)

- H2 keeps proof persistence synchronous in the artifact accept path transaction.
- `POST /artifacts` and `GET /artifacts/{artifact_id}` compute trust from persisted proof rows at response time.
- No async proof worker or `lean_pending` state is introduced in H2.
  - if async proofing is introduced later, it must be a separate milestone with explicit API lock updates.

### H2.4) Trust Promotion Rules (Locked)

`solver_trust` is a trust level label, not a solver status.

- promote to `solver_trust="proof_checked"` only when:
  - effective required rows exist
  - effective required rows are `backend="lean"` and `status="proved"`
  - effective required rows carry `semantics_version="adeu.lean.core.v1"`
- this promotion does not require validator runs (Option A locked)
- otherwise fallback stays:
  - `solver_trust="solver_backed"` when validator evidence exists
  - `solver_trust="kernel_only"` when validator evidence does not exist

### H2.5) Proof Trust Labels (Locked)

Use deterministic `proof_trust` labels:

- `lean_core_v1_proved`
  - promotion criteria met
- `lean_core_v1_partial_or_failed`
  - required lean rows exist but at least one required row failed or did not satisfy semantics/version constraints
- `mock_backend_not_proof_checked`
  - required rows exist but effective backend for at least one required key is not `lean`
- `no_required_proofs`
  - no effective rows found for one or more required keys

### H2.6) API Surface Lock

Additive-only API changes for legal artifact responses:

- Add `solver_trust` and `proof_trust` to:
  - `POST /artifacts` response
  - `GET /artifacts/{artifact_id}` response

Do not alter existing required fields or endpoint semantics.

### H2.7) Acceptance Tests (Locked)

- Mock backend path:
  - proofs may be `proved`, but trust remains `solver_backed + mock_backend_not_proof_checked`
- Lean backend failure path:
  - trust remains `solver_backed + lean_core_v1_partial_or_failed`
- Lean success path (deterministic stub/mocked lean backend in tests):
  - required obligations proved -> `proof_checked + lean_core_v1_proved`
- Missing required rows path:
  - never promote to `proof_checked`; emit `no_required_proofs`
- Duplicate proof row selection path:
  - latest-row selection rule determines effective trust outcome deterministically

### H2.8) Non-Goals (Locked)

- No proof promotion for concepts/puzzles in H2.
- No completeness claims.
- No artifact rejection due only to proof failure.

## Implementation Order (Frozen)

1. Milestone E0
2. Milestone E2
3. Milestone E1
4. Milestone F
5. Milestone G
6. Milestone H0 (retrospective gate)
7. Milestone H2 (proof pilot)

Milestone H1.1 hardening is optional and only pulled in if H0 finds gaps or UX pressure requires it.
