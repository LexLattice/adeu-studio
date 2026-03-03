# Draft Next Arc Options v6 (Post vNext+37, ASC Baseline)

This document is the fresh consolidated planning baseline for post-`vNext+37` sequencing, grounded to `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md` and current repo reality.

Status: active planning draft (`v17` through `v37` baselines executed; `v37` `K1` + `K2` merged on `main`; `vNext+38+` selection in progress).
Goal: define lock-respecting candidate paths for introducing deterministic semantic compilation and commitments IR without regressing v36/v37 boundary continuity.

## Naming Convention (Paths vs Bundles)

- `V31-*` identifiers remain historical and closed at `v37` closeout.
- `V32-*` identifiers are reserved for single path families in this next planning cycle.
- `B32-*` identifiers are reserved for explicit multi-path bundles only.
- Any selected arc must reference either one `V32-*` path or one `B32-*` bundle identifier; mixed shorthand is forbidden.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS36.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS36.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md`
- `docs/ASSESSMENT_vNEXT_PLUS37_EDGES.md`

This is a planning document only. It is not a lock doc and does not authorize runtime behavior changes.

## Baseline Agreement (Current Ground Truth)

- Locked continuation implementation baseline is `vNext+37` (`V31-G` persistence boundary release, `K1`-`K2`) and is merged on `main`.
- Latest closeout decision draft is `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS37.md`.
- Stop-gate schema family remains `stop_gate_metrics@1`.
- `V31` path family closure status is complete:
  - `V31-F` closed in `v36` (`J1` + `J2`).
  - `V31-G` closed in `v37` (`K1` + `K2`).
- Cross-arc continuity gates that must remain green in all `v38+` candidates:
  - v36 worker governance callgraph and deterministic denial contracts,
  - v37 proposer persistence source-of-truth and process-restart determinism contracts.

## ASC Semantic Interpretation Boundary (Planning Invariant)

- For ASC-path planning (`V32-*`), semantic authority must derive only from explicit semantic blocks (YAML frontmatter and/or fenced `adeu` blocks).
- Narrative prose remains non-authoritative for semantic hash derivation.
- Prose inference for lock/slice semantics is forbidden unless a future lock explicitly authorizes and defines deterministic parsing grammar.

## Repo-Relative Assessment of `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

### Directly Compatible with Existing Repo Patterns

- Deterministic canonical JSON + SHA-256 profile already exists and is used in multiple authoritative paths:
  - `apps/api/src/adeu_api/hashing.py`
  - `packages/urm_runtime/src/urm_runtime/hashing.py`
- Schema-export-plus-mirror discipline already exists:
  - authoritative package schema + mirrored `spec/*.schema.json` is established in `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`.
- Deterministic fixture/golden comparison style already exists:
  - exact-JSON equality fixture tests are established in `packages/adeu_kernel/tests/test_fixtures.py`.
- Deterministic closeout and lint posture already exists:
  - docs/artifact validation lints in `apps/api/scripts/` and stop-gate tooling in `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`.

### Greenfield Scope Introduced by `arcv6`

- No current package named `packages/adeu_commitments_ir`.
- No current package named `packages/adeu_semantic_compiler`.
- No existing semantic source blocks (` ```adeu... ` / semantic frontmatter) in lock docs outside `arcv6` examples.
- No existing compiler artifact family under `artifacts/semantic_compiler/<arc>/...`.
- No existing CI lane or lint entrypoint for semantic compiler governance checks.

### Lock Constraints That `arcv6` Must Respect in This Repo

- `v38+` introduction of semantic compiler work should remain non-`L2` unless a future boundary release is explicitly authorized.
- Existing `v36`/`v37` continuity guards remain merge-blocking and cannot be weakened.
- `stop_gate_metrics@1` remains frozen as schema family; any metric-key additions require explicit lock text and continuity handling.
- Canonical hashing profile remains frozen; compiler logic must not introduce profile forks.

## Lock Class Semantics (Operational)

- `L0`: internal hardening/tooling/guard-rail work with no externally visible contract change.
- `L1`: externally visible contract closure/behavior change on an existing surface (API/web/CLI/artifact contract), without boundary release.
- `L2`: boundary release (governance authority, persistence authority, provider/proposer surface expansion).

## Confirmed Post-v37 Gap Set (ASC-Oriented)

1. No typed commitments IR contract exists for lock/slice/stop-gate modules.
2. No deterministic semantic source grammar/parser exists for lock docs.
3. No deterministic compiler pass pipeline exists for source discovery -> parse -> normalize -> lock/reference checks.
4. No surface snapshot/delta engine exists for lock-declared surfaces in planning docs.
5. No deterministic PR-split/evidence-manifest artifact generation exists from a compiled lock model.
6. No CI/closeout integration exists for semantic compiler artifacts.

## Gap-to-Path Mapping (Total)

- Gap 1 -> `V32-A`
- Gap 2 -> `V32-B`
- Gap 3 -> `V32-C`
- Gap 4 -> `V32-D`
- Gap 5 -> `V32-D`
- Gap 6 -> `V32-E` (and optional `V32-F` for stop-gate metric integration)

Path dependency chain (planning authority):

- `V32-A -> V32-B -> V32-C -> V32-D -> V32-E -> V32-F(optional)`
- bundle selections (`B32-*`) may collapse steps only when all included path locks/acceptance remain explicitly preserved.

## Consolidated Path Families (v38+ Candidate Menu)

### Path V32-A: Commitments IR Contract Bootstrap

Lock class: `L1`

Lock-class rationale:
- `V32-A` introduces a new versioned schema contract mirrored under `spec/`, which is treated as externally visible contract surface in current ADEU taxonomy.

Goal:
- Introduce typed commitments IR contract and schema-export discipline in repo-native form.

Scope:
- Add `packages/adeu_commitments_ir` with deterministic Pydantic models and discriminated module union.
- Add schema export script that writes:
  - authoritative package schema file `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
  - mirror schema under `spec/adeu_commitments_ir.schema.json`
- Add deterministic schema regression tests.

Locks:
- Canonical JSON/hash profile remains frozen.
- Schema-export writer format for this path is frozen to existing repo schema-export convention (`json.dumps(..., indent=2, sort_keys=True) + "\\n"` in UTF-8).
- `extra="forbid"` and deterministic ordering on exported schema artifacts are required.
- module union discriminator key is frozen to `module_kind` for v0.
- strict polymorphic binding is required: each union member binds `module_kind` as a unique `Literal[...]`; fallback coercion is forbidden.
- schema naming/version convention is frozen to repo style (`*.v0_1.json` authoritative + `spec/*.schema.json` mirror).
- regeneration cleanliness guard is required: export rerun must fail closed on uncommitted generated schema deltas.
- Commitments IR v0 must remain compiler-agnostic in this arc:
  - no parser/pipeline assumptions are embedded into required schema fields beyond stable module contract primitives.
- No runtime API behavior changes and no stop-gate metric-key changes.

Acceptance:
- Commitments IR schema exports deterministically and mirrors correctly.
- Repeated export runs yield byte-identical schema output.

### Path V32-B: Semantic Source Grammar + Parser/Normalizer MVP

Lock class: `L1`

Goal:
- Define and enforce deterministic semantic source extraction from docs without prose inference.

Scope:
- Add semantic block grammar support:
  - optional YAML frontmatter,
  - fenced blocks labeled `adeu` / `adeu.*`.
- Implement deterministic source discovery, semantic block extraction, and normalization.
- Fail closed on unknown block schema, malformed blocks, duplicate module IDs, and ambiguous refs.
- Pilot on one selected historical lock doc fixture (for example `vNext+26`), not full repo rollout.

Locks:
- Semantic meaning is derived from explicit semantic blocks only.
- Narrative prose is non-authoritative for semantic hash derivation.
- Deterministic lexicographic ordering of discovered sources and normalized collections is required.

Acceptance:
- Parser/normalizer fixture corpus is deterministic across reruns.
- Same source bytes produce identical normalized payload hashes and diagnostics.

### Path V32-C: Compiler Core Passes (IR Build + Ref/Lock Typecheck)

Lock class: `L1`

Goal:
- Build deterministic compile pipeline core from normalized semantic records to typed commitments IR.

Scope:
- Add `packages/adeu_semantic_compiler` as compiler package root for core pass implementation in this path.
- Implement pass manager skeleton and core passes:
  - `DiscoverSources`
  - `ParseSemanticBlocks`
  - `Normalize`
  - `BuildIR`
  - `ResolveRefs`
  - `TypecheckLocks`
- Freeze minimal stdlib vocabulary (`EffectTag`, `LockKind`, `AssertionType`, `EvidenceType`, `TrustLane`, `EvidenceQualityLevel`) in compiler package.
- Emit deterministic diagnostics payload with stable ordering and reason-code identifiers.

Locks:
- Unknown stdlib tokens fail closed.
- Pass ordering and pass-hash output format are frozen for this path.
- No effect inference and no CI gating integration yet.

Acceptance:
- Compiler emits deterministic `commitments_ir.json` + `diagnostics.json` for pilot fixtures.
- Lock/ref/type violations are deterministic and machine-assertable.

### Path V32-D: Surface Snapshot + Delta Checks + PR Split Codegen

Lock class: `L1`

Goal:
- Add deterministic surface governance artifacts and generated implementation planning artifacts.

Scope:
- Add surface extraction for MVP surface kinds:
  - `schema`, `manifest`, `file`, `markdown_json_block`
- Add deterministic surface snapshot + baseline delta checks for freeze/additive rules.
- Add deterministic codegen artifacts:
  - `surface_snapshot.json`
  - `surface_diff.json` (when baseline exists)
  - `evidence_manifest.json`
  - `docs/generated/semantic_compiler/<arc>/PR_SPLITS.md`

Locks:
- Surface extraction and delta evaluation are deterministic and fail closed.
- Generated artifacts are derived only from compiled IR + selected source set.
- No stop-gate schema-family fork and no provider/runtime boundary changes.

Acceptance:
- Breaking surface deltas are deterministically rejected.
- PR split artifact is stable under unchanged semantic input.

### Path V32-E: CI Gate + Closeout Evidence Wiring (Keyset-Preserving)

Lock class: `L0`

Goal:
- Integrate semantic compiler outputs into CI/docs validation while preserving existing stop-gate metric keyset continuity.

Scope:
- Add deterministic lint entrypoint for semantic compiler compile/replay checks.
- Add CI lane wiring for selected participating docs.
- Add closeout-doc guard checks for semantic compiler evidence references (artifact existence + schema + hash contract).

Locks:
- `stop_gate_metrics@1` keyset remains unchanged in this path.
- Failure modes are deterministic with frozen exit-code contract.
- Existing v36/v37 continuity guards remain mandatory.

Acceptance:
- CI fails closed on missing/mismatched compiler evidence artifacts.
- Keyset continuity against current stop-gate baseline remains intact.

### Path V32-F: Optional Stop-Gate Metric Extension for Semantic Compiler

Lock class: `L1`

Goal:
- Add semantic compiler evidence hashes into stop-gate metrics as explicit machine-checkable gating inputs.

Scope:
- Introduce additive metric keys under `stop_gate_metrics@1` for semantic compiler artifact integrity.
- Update stop-gate tooling and closeout docs to consume those keys deterministically.

Locks:
- Requires explicit lock text authorizing metric-key expansion and continuity pivot.
- Must preserve schema family (`stop_gate_metrics@1`) with additive-only key evolution.
- Must retain compatibility with historical closeout artifacts.
- First-keyset-expansion continuity lock is frozen:
  - `V32-F` is treated as the first stop-gate metric-key expansion candidate since v26-era additive evolution,
  - lock selection must include explicit baseline-to-current keyset migration/evidence text before implementation.

Acceptance:
- New metric keys are deterministic, documented, and guard-covered.
- Historical metric parsing remains backward compatible.

## L2 Boundary Posture (Invariant)

- `V32` candidates are non-boundary paths by default (`L0`/`L1`).
- No `L2` boundary release is authorized by this options draft.
- Any future `L2` candidate in this family requires a dedicated lock update and explicit boundary precondition set.

## Decision Matrix (Thin-slice Selection)

| Option ID | Includes | Max lock class | Status | Benefit | Risk |
|---|---|---:|---|---|---|
| `V32-A` | `V32-A` | `L1` | open candidate | Establishes typed commitments contract and schema discipline | med |
| `V32-B` | `V32-B` | `L1` | open candidate | Defines deterministic semantic source grammar and parser baseline | med |
| `V32-C` | `V32-C` | `L1` | open candidate | Introduces compiler core pass pipeline with fail-closed typing | med/high |
| `V32-D` | `V32-D` | `L1` | open candidate | Adds surface governance and deterministic PR/evidence generation | high |
| `V32-E` | `V32-E` | `L0` | open candidate | Adds CI/docs guard wiring without metric-key churn | med |
| `V32-F` | `V32-F` | `L1` | optional candidate | Adds first-class stop-gate metrics for compiler evidence | high |
| `B32-ABC` | `V32-A + V32-B + V32-C` | `L1` | optional bundle | End-to-end semantic compile MVP in one arc family | high |
| `B32-CDE` | `V32-C + V32-D + V32-E` | `L1` | optional bundle | Full compiler + governance artifacts + CI integration | very high |

## Recommended Sequencing (Default)

1. `vNext+38` default: `V32-A` (commitments IR contract bootstrap).
2. `vNext+39` default: `V32-B` (semantic source grammar + parser/normalizer).
3. `vNext+40` default: `V32-C` (compiler core passes).
4. `vNext+41` candidate: `V32-D` (surface delta + PR/evidence generation).
5. `vNext+42` candidate: `V32-E` (CI/closeout integration, keyset-preserving).
6. Evaluate `V32-F` only after `V32-E` proves stable and only with explicit metric-key lock update.

## Standard Multi-Implementation Sequence (Required)

For each selected arc candidate (`vNext+38+`):

1. Draft parallel implementation briefs for multiple implementers (`codex`, `gpt`, `gemini`, `opus`) with identical locks/acceptance.
2. Run independent implementations and collect deterministic evidence bundles.
3. Produce comparative assessment (risk, lock adherence, determinism evidence, CI impact).
4. Consolidate into one lock candidate (new authority baseline after v37 remains `docs/LOCKED_CONTINUATION_vNEXT_PLUS37.md` until replaced).
5. Execute small-green PR sequence and close out with stop-gate decision note.

## Proposed Next Step

Prepare `vNext+38` release-selection baseline on `V32-A`:

1. Create `docs/ASSESSMENT_vNEXT_PLUS38_EDGES.md` scoped only to `V32-A` contract and schema-export edges.
2. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md` selecting `V32-A` only (single thin-slice default).
3. Keep v36/v37 continuity guards merge-blocking during `v38` implementation.
4. Defer parser/compiler pipeline work (`V32-B+`) to follow-on arcs unless explicitly bundled by lock decision.
