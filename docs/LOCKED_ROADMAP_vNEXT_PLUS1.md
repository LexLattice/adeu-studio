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

## Milestone H: Cross-Artifact Alignment + Proof Pressure Pilot (Later)

Do not start before G.

### H1) Alignment

- Shared vocabulary layer for term/sense mapping across documents.
- Conflicts/merges are surfaced as suggestions, not forced truth.

### H2) Proof Pilot

- Prove 1-2 narrow soundness invariants.
- `proof_checked` becomes meaningful for a limited, explicit slice.

## Implementation Order (Frozen)

1. Milestone E0
2. Milestone E2
3. Milestone E1
4. Milestone F
5. Milestone G

Then Milestone H as a separate larger track.
