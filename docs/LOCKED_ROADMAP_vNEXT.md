# Locked Roadmap vNext (Frozen)

This document captures the locked implementation plan, including final micro-locks, in the agreed order:

`A -> B -> C1 -> C2 -> D`

## Cross-Milestone Locks

- Trust metadata rollout is additive and scoped: only new/modified responses in these milestones (A diff/explain, B apply endpoint, C1 bridge endpoint, D questions endpoint). No repo-wide retrofit in one PR.
- No response may blur trust lanes. Every relevant response must separate:
  - `mapping_trust` (bridge/lifting/derivation confidence)
  - `solver_trust` (solver-backed evidence + pairing state)
  - `proof_trust` (Lean proof-checked, if any)

## Milestone A: Evidence-Coherent Tri-Lane UX + Trust Hygiene

Goal: instrument panel correctness + parity across lanes.

### A1) Pairing State (Single Source of Truth)

- `solver_pairing_state` lives only at:
  - `diff_report.summary.solver_pairing_state`
- Enum:
  - `PAIRED | UNPAIRABLE | MISSING_LEFT | MISSING_RIGHT | NO_RUNS`
- Also include in `diff_report.summary`:
  - `unpaired_left_keys: list[str]`
  - `unpaired_right_keys: list[str]`
- Never downgrade evidence to `NO_RUNS` when `UNPAIRABLE`.

### A2) Transaction Semantics (SQLite Explicit)

Accept/persist uses:

- single SQLite connection
- `PRAGMA foreign_keys=ON`
- `BEGIN IMMEDIATE`
- rollback-on-any-error for:
  - artifact insert
  - validator_runs inserts
  - proof_artifacts inserts
- commit only at end

### A3) Performance Caps (Deterministic Truncation)

- Legal repair feedback includes solver summary from latest run per attempt.
- Deterministic caps (for example): `max_lines`, `max_atoms`, stable truncation marker.

### A4) Web Smoke Baseline

- Add at least one route smoke test (headless).
- Add one mobile viewport check.

### A Scope

- Fix unpairable runs reporting.
- Add `/puzzles` route.
- Responsive layout hardening.
- Atomic persistence.
- Legal repair feedback includes solver evidence (capped).

### A Done When

- Pairing state is correct.
- Accept path is atomic.
- Puzzle lane parity exists in web route flow.
- Basic web smoke test is green.

## Milestone B: Concepts Ambiguity Actions + Patch Loop

Goal: resolve conceptual ambiguity without hand-editing JSON.

### B0) Schema Strategy (Locked)

- Keep `Ambiguity.options: list[str]` (legacy display options).
- Add:
  - `option_details_by_id: dict[str, AmbiguityOption]`
  - `option_labels_by_id: dict[str, str] | None` (optional convenience)
- Keys are stable `option_id` (not label).
- `AmbiguityOption` includes:
  - `option_id`
  - `label`
  - exactly one of `patch` or `variant_ir_id`
- UI renders options using `option_labels_by_id` when present; otherwise `AmbiguityOption.label`.

### B1) Apply Endpoint Defaults (Locked)

`POST /concepts/apply_ambiguity_option`

- `dry_run: bool = False`
- `include_validator_runs: bool = False`

Failure response:

- deterministic `errors[]` sorted by `(op_index, path, code)`
- each error includes: `op_index`, `path`, `code`, `message`

### B2) Patch Semantics

- Atomic and fail-closed: all ops apply or none.
- Sandbox allowlist prefixes enforced.
- Size/op count caps enforced.

### B3) ID Policy

- No ID canonicalization on apply.
- Patch validator must reject operations producing dangling references or inconsistent ID relations.
- Return deterministic patch validation errors (no silent fixups).

### B Scope

- Patch sandbox + allowlist + size caps.
- Proposer may emit `option_details_by_id` patches (optional in this milestone).
- Concepts UI ambiguity panel uses apply endpoint (with `dry_run` support).

### B Done When

- A bank-style ambiguity fixture is resolvable via UI action.
- Patch failures are deterministic.
- No schema break for existing fixtures/clients.

## Milestone C1: Bridge API (ADEU -> Concepts), API-First

Goal: deterministic lifting + concept analysis pipeline, without UI risk.

### C1.1) Reproducibility Fingerprint

Response includes:

- `bridge_mapping_version: str`
- `mapping_hash: str`
- deterministically sorted `bridge_manifest`

### C1.2) Trust Lane Split

- `mapping_trust` and `solver_trust` are separate.
- No ontology induction claims in this milestone.

### C1.3) Manifest Shape

- Stable ID maps.
- Provenance carryover tags:
  - `direct | derived | missing_provenance`

### C1 API

`POST /adeu/analyze_concepts` returns:

- `concept_ir`
- `check_report`
- `analysis`
- `bridge_manifest`
- optional `validator_runs` behind include flag

### C1 Done When

- Deterministic lift tests are green.
- Endpoint integration tests are green.

## Milestone C2: Legal Page Concept Panel (UI-Second, Minimal)

Goal: make bridge output usable in ADEU Studio with low scope risk.

### C2 Scope

- Add a Concept Analysis panel on ADEU page:
  - list terms/claims
  - closure/MIC/forced summary
  - click-to-highlight provenance spans in legal text
- Graph visualization is optional and out of scope for C2.

### C2 Done When

- Panel works end-to-end with span navigation.

## Milestone D: Socratic Question Loop (API-Only First)

Goal: convert evidence into actionable deterministic questions.

### D0) Separate Endpoint

Create:

- `POST /concepts/questions`

Inputs:

- `ir`
- optional `source_text`
- `mode`
- optional `include_forced_details`

Outputs:

- `questions[]` plus minimal metadata
- no mutation

### D1) Deterministic Templates

- Pure function of MIC/forced/countermodels/disconnect signals.
- Caps:
  - `max_questions=10`
  - `max_answers_per_q=4`
- Each answer is a patch action compatible with B option shape (`option_id`-aligned).

### D Done When

- Stable questions are generated on fixtures.
- Applying an answer via B patch endpoint deterministically advances state.

## Implementation Order (Frozen)

1. Milestone A
2. Milestone B
3. Milestone C1
4. Milestone C2
5. Milestone D

## Final Micro-Locks (Add, Then Freeze)

### 1) B Schema Join Invariant (Critical)

- `ambiguity.options` must be unique (no duplicates).
- `option_details_by_id` keys must be a subset of `ambiguity.options` (LAX) and an exact match in STRICT mode (optional but recommended if strict hygiene is desired).
- Rationale: prevents drift between legacy display options and actionable options.

### 2) B Backward-Compat Mapping Rule

- Current `ambiguity.options` tokens are often sense IDs. In dual payloads, default `option_id = existing option token` unless an explicit remap is provided.
- Rationale: avoids hidden semantic break and preserves stable identity.

### 3) A Transaction + Migrations Ordering

- Ensure schema/migrations/DDL are executed before entering accept-path write transaction.
- Accept-path write transaction is then:
  - open single connection
  - `PRAGMA foreign_keys=ON`
  - `BEGIN IMMEDIATE`
  - write artifact + runs + proofs
  - rollback on any error
- Rationale: SQLite DDL can implicitly commit; this preserves true atomicity.

### 4) A Unpaired Key Format Lock

- Canonical unpaired key string:
  - `"{request_hash}:{formula_hash}"`
- `unpaired_left_keys` and `unpaired_right_keys` are sorted lexicographically by that string.
- Rationale: stable client parsing + deterministic diffs.

### 5) C1 Mapping Hash Recipe Lock

- `mapping_hash = sha256(canonical_json({ bridge_mapping_version, mapping_rules, static_config }))`
- `canonical_json` must be:
  - UTF-8
  - sorted keys
  - no whitespace
  - stable list ordering
- Rationale: reproducible bridge outputs across environments.
