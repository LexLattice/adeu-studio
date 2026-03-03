# Assessment vNext+41 Edges (V32-D Planning)

This document records pre-implementation edge analysis for `vNext+41` (`V32-D` surface snapshot/delta + PR/evidence codegen), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.

Status: active planning assessment (pre-implementation, March 3, 2026 UTC).

## Scope

- In scope: deterministic surface extraction, deterministic surface snapshot/delta evaluation, deterministic evidence-manifest generation, deterministic `PR_SPLITS` codegen, and deterministic guard tests.
- Out of scope: semantic-source parser contract evolution (`V32-B`), compiler-core pass-sequence/diagnostics contract evolution (`V32-C`), CI lane integration (`V32-E`), stop-gate metric-key expansion (`V32-F`), and runtime/provider/proposer boundary changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md`
- `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
- `packages/adeu_semantic_compiler/tests/test_semantic_compiler_compile.py`
- `packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py`
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`
- `apps/api/scripts/lint_closeout_consistency.py`

## Repository Baseline Anchors

1. v40 compiler-core outputs already exist and are deterministic:
   - `artifacts/semantic_compiler/v40/commitments_ir.json`
   - `artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json`
   - `artifacts/semantic_compiler/v40/pass_manifest.json`
2. Semantic compiler package baseline is implemented and authoritative:
   - `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
3. `V32-D` output family is currently absent and remains greenfield for v41:
   - no committed `artifacts/semantic_compiler/v41/surface_snapshot.json`
   - no committed `artifacts/semantic_compiler/v41/surface_diff.json`
   - no committed `artifacts/semantic_compiler/v41/evidence_manifest.json`
   - no committed `docs/generated/semantic_compiler/v41/PR_SPLITS.md`
4. Deterministic canonical JSON profile remains frozen and available:
   - `canonical_json` / `sha256_canonical_json` in `apps/api/src/adeu_api/hashing.py` and `packages/urm_runtime/src/urm_runtime/hashing.py`.
5. Stop-gate schema/keyset continuity remains active and must be preserved:
   - schema family remains `stop_gate_metrics@1`,
   - derived metric-key cardinality remains `79` through v40 closeout.
6. v36/v37/v38/v39/v40 continuity contracts are active and must remain green through v41.

## V32-D Edge Set

1. Surface-registry drift:
   - unstable ordering of extracted surfaces can produce nondeterministic snapshot bytes.
2. Selector-normalization drift:
   - inconsistent path normalization can create "same surface, different signature" behavior.
3. Surface-kind ambiguity:
   - unsupported/unknown surface kinds can be silently accepted without explicit fail-closed policy.
4. Markdown JSON block extraction ambiguity:
   - multiple candidate fenced JSON blocks can produce non-deterministic selector binding.
5. Schema/manifest hashing drift:
   - extractor implementations can diverge on canonicalization and produce non-replayable hashes.
6. Baseline-bootstrap ambiguity:
   - missing prior snapshot baseline can trigger inconsistent delta behavior unless explicitly locked.
7. Delta-rule semantics drift:
   - `freeze`, `additive_only`, and `exact_set` checks can diverge without frozen violation policy.
8. Additive-only false positives/negatives:
   - structural compatibility checks can under- or over-report breaking deltas.
9. Evidence-manifest schema drift:
   - required evidence fields can drift across reruns if required-field set is not frozen.
10. PR split generation drift:
    - ordering and grouping can differ across implementations without deterministic tie-breakers.
11. Output-path leakage:
    - generated artifacts can escape intended roots unless output paths are frozen and enforced.
12. Input-handoff drift:
    - v41 can consume invalid v40 inputs unless diagnostics/pass-manifest handoff is explicitly fail-closed.
13. Over-scope risk into `V32-E`:
    - implementation can accidentally introduce CI gate wiring in a non-v41 scope arc.
14. Over-scope risk into `V32-F`:
    - implementation can accidentally introduce stop-gate metric-key expansion.
15. Generated-artifact cleanliness drift:
    - regenerated artifacts can diverge from committed bytes without explicit cleanliness guards.
16. Continuity regression risk:
    - v41 toolchain changes can weaken existing v36/v37/v38/v39/v40 guard expectations.
17. Symlink signature ambiguity:
    - file-surface selectors that resolve to symlink entries can produce implementation divergence unless symlink handling is explicitly fail-closed.
18. Bootstrap review flooding risk:
    - deterministic `no_baseline` mode marks all current surfaces as adds and can produce unreviewable first-run PR split artifacts in large selector sets.
19. PR split reviewability drift:
    - module-scoped grouping can become too large for practical review unless deterministic chunking policy is explicitly introduced in a future lock.
20. Semantic-equivalency ambiguity:
    - strict hash-equality deltas can flag cosmetically equivalent structured content unless a future semantic-equivalency lane is explicitly designed and locked.

## Required Guardrails

- Input-handoff lock: v41 consumes only frozen v40 compiler outputs; v40 `ERROR` diagnostics and incomplete pass-manifest chain fail closed.
- Surface-kind lock: supported kinds are exactly `schema`, `manifest`, `file`, `markdown_json_block`.
- Selector-normalization lock: POSIX normalization, deterministic dot-segment collapse, no absolute paths, no symlink-based signature basis.
- Symlink policy lock: `file` surface selectors resolving to symlink entries are invalid and fail-closed in v41.
- Surface-registry ordering lock: deterministic `surface_id` lexicographic ordering.
- Baseline-bootstrap lock: absent v40 baseline snapshot triggers deterministic `no_baseline` diff mode.
- Delta-policy lock: `freeze`, `additive_only`, `exact_set` are the only supported rule modes and violations are fail-closed.
- Delta-equivalency lock: semantic-equivalency bypass behavior is out-of-scope in v41 and must remain absent.
- Output-contract lock: v41 emits only `surface_snapshot`, `surface_diff`, `evidence_manifest`, and `PR_SPLITS` at frozen paths.
- Output-path lock: writes outside `artifacts/semantic_compiler/v41` and `docs/generated/semantic_compiler/v41` are invalid.
- Evidence-manifest lock: required top-level key set and artifact-hash section behavior are frozen and deterministic.
- PR-splits lock: stable ordering by `(slice_id, module_id)` is required.
- Diagnostics continuity lock: compiler diagnostics namespace continuity remains `SCC[0-9]{4}`.
- Hash-profile continuity lock: canonical JSON SHA-256 profile remains frozen and reused.
- Scope fence: no `V32-E` CI/closeout integration behavior in v41.
- Scope fence: no `V32-F` metric-key expansion in v41.
- Continuity fence: no changes to v36/v37/v38/v39/v40 runtime or guard contracts.

## Acceptance Evidence Targets (v41)

- Deterministic `surface_snapshot`, `surface_diff`, `evidence_manifest`, and `PR_SPLITS` artifacts are present for v41 fixtures.
- Reruns under fixed v40 compiler inputs are byte-identical for all v41 artifacts.
- Delta-rule violations are deterministic and fail-closed.
- CI remains green with v36/v37/v38/v39/v40 continuity guards still active.

## Implementation Readiness Notes

1. `V32-D` is implementation-ready as a standalone `L1` thin slice on top of closed v40 outputs.
2. Highest risk is nondeterministic surface selector handling and delta-rule interpretation drift.
3. Recommended implementation order:
   - deterministic surface extraction + registry ordering,
   - snapshot + delta generation with bootstrap baseline policy,
   - evidence-manifest + PR split codegen,
   - deterministic/fail-closed guard suite.

## Deferred Expansions (Non-v41)

- CI/closeout lane integration is deferred to explicit `V32-E` lock text.
- Stop-gate metric-key additions for semantic-compiler evidence are deferred to explicit `V32-F` lock text.
- Resolver namespace aliasing/workspace-scoped bindings remain deferred and out of this arc.
- Bootstrap overflow controls and deterministic PR split chunking are deferred to explicit follow-on lock text.
- Semantic-equivalency delta evaluation for structured surfaces is deferred to explicit follow-on lock text.
