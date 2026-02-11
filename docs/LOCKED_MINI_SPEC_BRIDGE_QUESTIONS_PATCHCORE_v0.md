# Locked Mini-Spec: Bridge + Questions + Mapping Trust + Patch Core (v0)

This document freezes a focused follow-on slice in four areas:

1. Bridge loss transparency (`/adeu/analyze_concepts`)
2. Question rationale enrichment (`/concepts/questions`, `/adeu/questions`)
3. Mapping trust enum freeze (API type hygiene)
4. Shared patch-core extraction (no semantic drift)

Status: additive-only spec, no solver semantics changes.

## Global Locks

- No solver semantic changes in ADEU, Concepts, or Puzzles.
- No breaking API changes in this slice.
- Determinism required for all new list fields:
  - explicit sort keys
  - stable tie-breakers
  - permutation invariance tests
- Existing trust lanes remain separate:
  - `mapping_trust`
  - `solver_trust`
  - `proof_trust`

## M1) Bridge Loss Report (Additive)

### Goal

Make ADEU -> Concepts projection explicit about preserved vs projected vs not-modeled semantics.

### Endpoint Lock

Add field to `POST /adeu/analyze_concepts` response:

- `bridge_loss_report: BridgeLossReport`

This is additive; existing fields remain unchanged.

### Schema Lock

`BridgeLossReport` fields:

- `version: "adeu.bridge.loss.v1"`
- `entries: list[BridgeLossEntry]`
- `summary: BridgeLossSummary`

`BridgeLossFeature` frozen vocabulary:

- `norm_modality`
- `exception_effect`
- `scope_time`
- `scope_jurisdiction`
- `condition_predicate`

Versioning lock:

- This vocabulary is frozen for `adeu.bridge.loss.v1`.
- Adding or renaming `feature_key` values requires a version bump (for example, `adeu.bridge.loss.v2`).

`BridgeLossEntry` fields:

- `feature_key: BridgeLossFeature`
- `scope: "structural" | "instance"`
- `status: "preserved" | "projected" | "not_modeled"`
- `detail: str`
- `source_paths: list[str]` (ADEU JSON Pointer paths only)
- `notes: str | null`

`BridgeLossSummary` fields:

- `preserved_count: int`
- `projected_count: int`
- `not_modeled_count: int`

### Determinism Lock

- `entries` sorted by `(feature_key, scope, status)` ascending.
- `(feature_key, scope, status)` must be unique within a report for a given bridge version.
- `source_paths` sorted lexicographically.
- `summary` derived from `entries` only.
- `structural` entries are bridge-version facts (independent of input instance).
- `instance` entries are request-specific and must reference concrete `source_paths`.
- `structural` entries must use `source_paths: []`.

### Acceptance

- Same IR -> identical `bridge_loss_report`.
- Permuted ADEU input order -> identical `bridge_loss_report`.
- Structural entries remain identical across all IR instances for the same bridge version.
- Response remains backward compatible for clients that ignore the new field.

## M2) Question Rationale (Additive, Deterministic)

### Goal

Explain why each question is asked, using deterministic analysis signals rather than free-form generation.

### Endpoint Lock

Add to question objects returned by:

- `POST /concepts/questions`
- `POST /adeu/questions`

New fields:

- `rationale: str`
- `rationale_code: "mic_conflict" | "forced_nonentailment" | "disconnected_cluster"`

New response metadata fields:

- `/concepts/questions`: `rationale_version: "concepts.rationale.v1"`
- `/adeu/questions`: `rationale_version: "adeu.rationale.v1"`

### Generation Lock

- `rationale_code` is derived directly from existing `signal` using this frozen mapping:
  - `mic -> mic_conflict`
  - `forced_countermodel -> forced_nonentailment`
  - `disconnected_clusters -> disconnected_cluster`
- `rationale` is produced from fixed templates keyed by `rationale_code`.
- No LLM call allowed for rationale generation in this milestone.
- `signal` remains the canonical machine-facing discriminator.
- `rationale_code` is a user-facing explanation label derived from `signal`.

### Determinism Lock

- For same question payload, `rationale` and `rationale_code` must be identical.
- Rationale templates are versioned by constants and exposed via `rationale_version`.

### Acceptance

- Existing question IDs/ranking unchanged by adding rationale fields.
- Same input -> identical rationale fields.
- Permutation invariance holds for rationale fields.

### Non-Goal

- In this milestone, rationale text does not surface bridge-loss metadata (for example, projected/not-modeled bridge-loss details).

## M3) Mapping Trust Enum Freeze

### Goal

Prevent string drift for mapping trust labels.

### Type Lock

Introduce shared alias in API layer:

- `MappingTrust = Literal["derived_bridge", "derived_alignment"]`

For responses where mapping is not applicable, continue using nullable field:

- `mapping_trust: MappingTrust | None`

### Usage Lock

Replace free-form `str` typing for mapping-trust fields in all API response models that emit `mapping_trust`.

Field presence lock:

- `mapping_trust` is always present in responses that declare it.
- When not applicable, emit `mapping_trust: null` (do not omit key).

### Non-Goal

- No new mapping trust labels in this milestone.

### Acceptance

- Static typing/lint prevents accidental ad-hoc mapping trust strings.
- Existing emitted values unchanged.

## M4) Patch-Core Consolidation (No Behavior Change)

### Goal

Extract shared JSON patch machinery to reduce duplication without changing domain behavior.

### Scope Lock

Create shared package:

- `packages/adeu_patch_core/`

Shared-only responsibilities:

- JSON pointer parsing and traversal
- RFC6902 op primitives (`add`, `remove`, `replace`, `move`, `copy`, `test`)
- deterministic patch-size accounting utilities
- deterministic base error normalization utilities

Shared error model lock:

- `adeu_patch_core` defines its own internal error dataclass for patch operation failures.
- Domain wrappers translate core errors into existing domain error shapes/contracts.

Dependency lock:

- `packages/adeu_patch_core` depends only on `adeu_ir` at runtime.
- Add a package-local `pyproject.toml` consistent with existing package conventions.

Keep domain-specific logic in place:

- path allowlists
- reference-integrity checks
- domain error codes and policy decisions

### API Contract Lock

- `/concepts/apply_patch` and `/concepts/apply_ambiguity_option` response/error contracts must remain unchanged.
- Any ADEU patch endpoint behavior must remain unchanged.

### Determinism Lock

- Error ordering remains sorted by `(op_index, path, code)`.
- Operation application remains atomic (all-or-none).

Parity lock (required for Phase A):

- For success fixtures:
  - patched output canonical JSON must be byte-identical to legacy engine output.
- For failure fixtures:
  - ordered `(op_index, path, code)` tuples must be identical to legacy behavior.

### Migration Lock

- Do extraction in two phases:
  - Phase A: introduce shared core and dual-run parity tests.
  - Phase B: switch callers to shared core after parity is green.

### Acceptance

- Existing patch fixtures pass unchanged.
- New parity tests prove old vs new engines match for the shared op layer.
- No schema or response shape regressions.

## Implementation Sequence (Frozen)

1. M3 Mapping trust enum freeze (smallest risk)
2. M2 Question rationale fields
3. M1 Bridge loss report
4. M4 Patch-core extraction (A/B phases)

## Commit Plan (Small Green Commits)

1. `api: freeze MappingTrust literal and wire nullable usage`
2. `questions: add deterministic rationale_code and rationale fields`
3. `bridge: add additive bridge_loss_report to adeu/analyze_concepts`
4. `patch-core: add shared core package with parity fixtures`
5. `patch-core: switch concepts/kernel patch internals to shared core`
6. `eval: update question fixtures/dashboard adapters for rationale fields`
7. `eval: update bridge-response fixtures/adapters for bridge_loss_report handling (or explicit ignore)`

## Trust-Policy Note

- `kernel_only`: unchanged for flows without solver evidence.
- `solver_backed`: unchanged for flows with validator/solver evidence.
- `proof_checked`: unchanged; this mini-spec does not alter proof promotion.
- `mapping_trust`: tightened type safety only (`derived_bridge|derived_alignment|null`), semantics unchanged.
