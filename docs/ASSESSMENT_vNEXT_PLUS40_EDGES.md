# Assessment vNext+40 Edges (V32-C Planning)

This document records pre-implementation edge analysis for `vNext+40` (`V32-C` compiler core pass pipeline), aligned to `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.

Status: historical planning assessment (implementation completed on `main`, March 3, 2026 UTC).

## Closeout Addendum (Post-Implementation)

- `O1` (`V32-C` compiler core pass pipeline MVP) merged via PR `#226`.
- `O2` (`V32-C` compiler core determinism/fail-closed guards) merged via PR `#227`.
- Semantic-compiler package now exists at `packages/adeu_semantic_compiler`.
- v40 closeout artifacts are present:
  - `artifacts/quality_dashboard_v40_closeout.json`
  - `artifacts/stop_gate/metrics_v40_closeout.json`
  - `artifacts/stop_gate/report_v40_closeout.md`
- Compiler-core closeout artifacts are generated deterministically at:
  - `artifacts/semantic_compiler/v40/commitments_ir.json`
  - `artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json`
  - `artifacts/semantic_compiler/v40/pass_manifest.json`
- Stop-gate metric keyset continuity is preserved (`v39` -> `v40` exact-set equality; cardinality `79`).

## Scope

- In scope: compiler core pass-manager skeleton, deterministic pass sequencing, IR build/ref resolution/typecheck, deterministic compiler diagnostics and pass-manifest outputs, deterministic guard tests.
- Out of scope: semantic-source parser contract evolution, surface snapshot/delta/codegen, CI lane expansion, stop-gate metric-key expansion.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS39.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md`
- `packages/adeu_semantic_source/src/adeu_semantic_source/compile.py`
- `packages/adeu_commitments_ir/src/adeu_commitments_ir/models.py`
- `apps/api/src/adeu_api/hashing.py`
- `packages/urm_runtime/src/urm_runtime/hashing.py`
- `apps/api/scripts/lint_closeout_consistency.py`

## Repository Baseline Anchors

1. Semantic-source contract baseline now exists and is closed in v39:
   - `packages/adeu_semantic_source/src/adeu_semantic_source/compile.py`
   - `artifacts/semantic_compiler/v39/semantic_source.normalized.json`
   - `artifacts/semantic_compiler/v39/semantic_source.diagnostics.json`
2. Commitments IR contract baseline is closed in v38:
   - `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
   - `spec/adeu_commitments_ir.schema.json`
3. Deterministic canonical JSON profile is frozen and available:
   - `canonical_json`/`sha256_canonical_json` in `apps/api/src/adeu_api/hashing.py` and `packages/urm_runtime/src/urm_runtime/hashing.py`.
4. Compiler-core package baseline is now implemented:
   - `packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py`
   - deterministic guard suite in `packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py`.
5. Stop-gate schema family and keyset continuity are active constraints:
   - `stop_gate_metrics@1` remains the only schema family,
   - v39 closeout preserved exact v38 keyset equality with derived cardinality `79`,
   - v36/v37/v38/v39 closeout artifacts each report derived cardinality `79` (no keyset drift across these arcs).
6. v36/v37/v38/v39 continuity contracts are active and must remain green through v40.

## V32-C Edge Set

1. Pass-order drift:
   - compiler pass order can diverge across implementations without a frozen sequence contract.
2. Input-handoff drift:
   - compiler may bypass semantic-source normalized contract and re-parse docs directly unless input boundary is explicit.
3. IR-build non-determinism:
   - commitments IR output ordering can drift across reruns if sorting/canonicalization are not frozen.
4. Reference-resolution instability:
   - unresolved/duplicate references can produce non-deterministic diagnostics unless fail-closed and ordered.
5. Typecheck ambiguity drift:
   - lock typecheck behavior can vary without a frozen lock/assertion typing contract.
6. Stdlib token drift:
   - token vocabulary can fork unless unknown-token behavior is fail-closed and versioned.
7. Diagnostics contract drift:
   - reason-code namespace, ordering, and index-base can drift and break byte-level reproducibility.
8. Pass-manifest drift:
   - pass execution evidence shape/order can drift unless explicit pass-manifest contract is frozen.
9. Artifact-path drift:
   - compiler outputs can leak outside canonical artifact roots without explicit output-path restrictions.
10. Hash-profile drift:
   - compiler artifacts can introduce hashing-profile forks if canonical JSON profile is not explicitly reused.
11. Over-scope risk into `V32-D`:
   - compiler-core implementation can accidentally include surface snapshot/delta/codegen behavior.
12. Over-scope risk into `V32-E`:
   - compiler-core implementation can accidentally include CI gate/closeout integration behavior.
13. Continuity regression risk:
   - v40 compiler changes can weaken existing v36/v37/v38/v39 guard expectations.
14. Silent-acceptance risk:
   - malformed semantic-source handoff payloads may be tolerated unless strict fail-closed gates are mandatory.
15. Replay cleanliness drift:
   - generated compiler artifacts can diverge from committed bytes without explicit cleanliness guards.
16. Trust-lane boundary drift:
   - compiler diagnostics can be misused as runtime/trust-lane enforcement without explicit non-runtime lock text.

## Required Guardrails

- Pass-sequence lock: compiler pass order is frozen and machine-checkable.
- Pass-boundary lock: early compiler passes are load/validate-only and may not parse markdown source in v40.
- Entrypoint lock: compiler uses one authoritative command entrypoint only.
- Input-boundary lock: compiler consumes semantic-source normalized artifacts only; direct doc parsing is forbidden in this path.
- Input-diagnostics handoff lock: v39 diagnostics with any `error` fail closed for v40 handoff; non-error diagnostics are carried forward deterministically.
- Output-contract lock: compiler emits only commitments IR + compiler diagnostics + pass-manifest artifacts in this arc.
- IR-ordering lock: commitments IR serialization order is deterministic (modules by `(module_kind, id)`, nested collections by stable-ID lexicographic order).
- Output-path lock: compiler artifacts are emitted only under `artifacts/semantic_compiler/v40`.
- Contract-id equivalence lock: `adeu_commitments_ir@0.1` remains equivalent to authoritative schema `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`.
- Stdlib lock: unknown vocabulary tokens fail closed; vocabulary version is frozen for v40.
- Stdlib naming lock: compiler uses `EvidenceQuality` token family label mapped to commitments IR `CommitmentsEvidenceQuality`.
- Strictness lock: unresolved refs, type mismatches, and ambiguous bindings fail closed.
- Diagnostics lock: `SCC[0-9]{4}` namespace, deterministic ordering, 1-based indexing, and empty-string fallback for missing `module_id` are frozen.
- Module-id derivation lock: diagnostics `module_id` is sourced only from normalized semantic block declared metadata; synthetic IDs are forbidden.
- Diagnostic-position-source lock: diagnostics positions are source-path oriented; normalized-JSON offsets are forbidden, with deterministic `start_line = 1` fallback when mapping is unavailable.
- Pass-manifest chain lock: `pass_manifest` entries include `{name, index, input_sha256, output_sha256}` for deterministic chain-of-custody.
- Pass-hash-subject lock: per-pass hash subject is canonical JSON bytes of the pass input/output value.
- Pass-hash-identity lock: read-only passes may keep identical input/output hashes, while mutating passes doing so are treated as contract violations.
- Pass-hash-identity partition lock: mutating pass set is fixed (`BuildIR`, `ResolveRefs`) and read-only pass set is fixed (`LoadCollection`, `ValidateBlocks`, `RevalidateNormalization`, `TypecheckLocks`).
- Deterministic-normalization lock: output serialization and ordering are deterministic and byte-reproducible.
- Hash-profile continuity lock: canonical JSON/hash profile remains frozen and reused.
- Scope fence: no `V32-D` surface snapshot/delta/codegen behavior in v40.
- Scope fence: no `V32-E` CI/closeout integration behavior in v40.
- Continuity fence: no changes to v36/v37/v38/v39 runtime boundary behaviors or guard expectations.
- Keyset fence: no new stop-gate metric keys and no schema-family fork in v40.

## Acceptance Evidence Targets (v40)

- Compiler core pass pipeline MVP is present for semantic-source -> commitments-IR compile flow.
- Commitments IR, diagnostics, and pass-manifest outputs are deterministic across reruns under fixed inputs.
- Compiler diagnostics are deterministic and fail-closed for unresolved/type-invalid inputs.
- CI remains green with existing v36/v37/v38/v39 continuity guards still active.

## Implementation Readiness Notes

1. `V32-C` is implementation-ready as a standalone `L1` thin slice.
2. Highest risk is pass-order and typecheck drift producing non-reproducible diagnostics.
3. Recommended implementation order:
   - pass-manager skeleton with frozen `LoadCollection -> ValidateBlocks -> RevalidateNormalization` boundary,
   - IR build/ref resolve/typecheck,
   - deterministic output contracts + fail-closed guard suite.

## Deferred Ergonomics/Scale Expansions (Non-v40)

- Partial-run compiler ergonomics (`--stop-after`, intermediate IR dumps) are deferred to explicit follow-on lock text.
- Resolver namespace aliasing/workspace-scoped bindings are deferred to explicit follow-on lock text.

## Completion Trace

1. `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md` was finalized to `V32-C` scope and closed post-merge.
2. `v40` executed as two small-green PRs:
   - PR `#226`: compiler core pass pipeline MVP.
   - PR `#227`: compiler core deterministic/fail-closed guard suite.
3. v36/v37/v38/v39 continuity checks remained mandatory and green throughout v40 closeout.
