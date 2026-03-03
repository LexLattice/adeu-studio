# Locked Continuation vNext+40 (Closed Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS39.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: closed lock (implemented on `main`, March 3, 2026 UTC).

Decision basis:

- `vNext+39` (`N1`-`N2`) is merged on `main` via PR `#224` and PR `#225` with green CI checks.
- `vNext+39` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md` with `all_passed = true`.
- Post-v39 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Selected v40 thin-slice default is semantic-compiler core candidate:
  - `V32-C` (compiler core pass pipeline MVP).
- `vNext+40` is constrained to deterministic additive hardening for `V32-C` only:
  - no solver/runtime semantics release,
  - no governance/persistence boundary release expansion,
  - no surface snapshot/delta/codegen release in this arc.
- `vNext+40` (`O1`-`O2`) is now merged on `main` via PR `#226` and PR `#227` with green CI checks.
- `vNext+40` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md` with `all_passed = true`.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS39.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v40,
  - v40 keyset must be exactly equal to v39 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v40 start is `79` and must remain unchanged in this arc,
  - repository closeout artifacts for v36/v37/v38/v39 each report derived metric-key cardinality `79`,
  - keyset authority is `stop_gate_metrics@1` payload field `metrics` object keys only,
  - keyset extraction/comparison in this arc is from closeout artifacts produced by `apps/api/scripts/build_stop_gate_metrics.py` and validated by deterministic docs lint `apps/api/scripts/lint_closeout_consistency.py` using exact-set equality.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36 continuity guarantees remain frozen as release preconditions:
  - worker-route governance release contract (`V31-F`, `J1`) remains authoritative,
  - v36 governance-release guard suite (`V31-F`, `J2`) remains authoritative baseline.
- v37 continuity guarantees remain frozen as release preconditions:
  - proposer persisted idempotency source-of-truth contract (`V31-G`, `K1`) remains authoritative,
  - v37 persistence-release guard suite (`V31-G`, `K2`) remains authoritative baseline.
- v38 continuity guarantees remain frozen as release preconditions:
  - commitments IR schema authority/mirror parity contract (`V32-A`, `M1`) remains authoritative,
  - v38 commitments deterministic guard suite (`V32-A`, `M2`) remains authoritative baseline.
- v39 continuity guarantees remain frozen as release preconditions:
  - semantic-source parser/normalizer contract (`V32-B`, `N1`) remains authoritative,
  - v39 semantic-source deterministic guard suite (`V32-B`, `N2`) remains authoritative baseline.
- Boundary-release scope lock for v40 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for ASC-path work derives only from explicit semantic blocks,
  - narrative prose is non-authoritative for semantic hash derivation,
  - prose-inference parsing is forbidden unless explicitly authorized by a future lock.
- Closeout observability continuity lock is frozen:
  - v40 closeout must include a runtime-observability comparison row against v39 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `O1` compiler core pass pipeline MVP (`V32-C`)
2. `O2` compiler core determinism/fail-closed guard suite (`V32-C`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- commitments IR schema evolution release (`V32-A`) in this arc,
- semantic-source grammar/parser surface evolution release (`V32-B`) in this arc,
- surface snapshot/delta/codegen release (`V32-D`) in this arc,
- semantic-compiler CI gate integration release (`V32-E`) in this arc,
- stop-gate metric-key expansion for semantic compiler evidence (`V32-F`) in this arc,
- compiler partial-execution CLI (`--stop-after`) in this arc,
- any provider or proposer endpoint expansion,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v40)

- v41+ surface snapshot/delta + PR/evidence codegen (`V32-D`).
- v42+ CI/closeout evidence wiring (`V32-E`).
- v43+ optional stop-gate metric extension for semantic compiler evidence (`V32-F`) via explicit lock update.
- v44+ compiler developer ergonomics (`--stop-after`, intermediate IR dumps) under explicit lock text.
- v45+ resolver namespace aliasing/workspace-scoped bindings under explicit lock text.

## V39 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS39.md",
  "target": "V32-C",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v40.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V32-C Compiler Core Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32c_compiler_core_contract@1",
  "package_root": "packages/adeu_semantic_compiler",
  "export_entrypoint": "packages/adeu_semantic_compiler/src/adeu_semantic_compiler/compile.py",
  "export_call_pattern": "python -m adeu_semantic_compiler.compile",
  "input_contract_id": "semantic_source_collection@0.1",
  "input_diagnostics_contract_id": "semantic_source_diagnostics@0.1",
  "input_diagnostics_handoff_policy": {
    "errors": "fail_closed",
    "warnings": "carry_forward_to_v40_diagnostics"
  },
  "output_ir_contract_id": "adeu_commitments_ir@0.1",
  "output_diagnostics_contract_id": "semantic_compiler_diagnostics@0.1",
  "output_pass_manifest_contract_id": "semantic_compiler_pass_manifest@0.1",
  "pass_sequence": [
    "LoadCollection",
    "ValidateBlocks",
    "RevalidateNormalization",
    "BuildIR",
    "ResolveRefs",
    "TypecheckLocks"
  ],
  "pass_sequence_ordering": "frozen",
  "pass_phase_boundary": {
    "front_end_markdown_parsing": "forbidden_in_v32c",
    "input_mode": "semantic_source_normalized_only"
  },
  "stdlib_vocab_version": "v32c_frozen_v1",
  "stdlib_vocab_families": [
    "EffectTag",
    "LockKind",
    "AssertionType",
    "EvidenceType",
    "TrustLane",
    "EvidenceQuality"
  ],
  "stdlib_vocab_equivalence": {
    "EvidenceQuality": "CommitmentsEvidenceQuality"
  },
  "stdlib_unknown_tokens": "error",
  "contract_id_equivalence": {
    "adeu_commitments_ir@0.1": "packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json"
  },
  "diagnostic_code_namespace": "SCC",
  "diagnostic_code_pattern": "^SCC[0-9]{4}$",
  "diagnostic_sort_order": [
    "module_id",
    "path",
    "start_line",
    "code"
  ],
  "diagnostic_missing_module_id_sort_value": "",
  "diagnostic_module_id_policy": {
    "source": "normalized_semantic_block_metadata_declared_module_id",
    "when_missing": "",
    "synthetic_ids": "forbidden"
  },
  "diagnostic_position_base": {
    "line": 1,
    "column": 1
  },
  "diagnostic_position_resolution": {
    "coordinate_space": "source_path_relative",
    "line_policy": "source_handoff_if_available_else_1",
    "normalized_json_offsets": "forbidden"
  },
  "output_artifacts": {
    "commitments_ir": "artifacts/semantic_compiler/v40/commitments_ir.json",
    "diagnostics": "artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json",
    "pass_manifest": "artifacts/semantic_compiler/v40/pass_manifest.json"
  },
  "output_ir_ordering": {
    "modules": [
      "module_kind",
      "id"
    ],
    "nested_collections": "stable_id_lexicographic"
  },
  "pass_manifest_entry_fields": [
    "name",
    "index",
    "input_sha256",
    "output_sha256"
  ],
  "pass_manifest_hash_chain": "required_per_pass",
  "pass_hash_subject": "canonical_json_bytes_of_pass_value",
  "pass_hash_identity_policy": {
    "mutating_passes": [
      "BuildIR",
      "ResolveRefs"
    ],
    "allow_equal_input_output_for_read_only_passes": [
      "LoadCollection",
      "ValidateBlocks",
      "RevalidateNormalization",
      "TypecheckLocks"
    ],
    "equal_hash_on_mutating_passes": "error"
  },
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## O1) Compiler Core Pass Pipeline MVP (`V32-C`)

### Goal

Introduce deterministic compiler-core pass execution from normalized semantic source into typed commitments IR.

Lock-class rationale:

- this slice is `L1` because it introduces a new deterministic compiler-core contract surface and artifacts consumed by follow-on governance/codegen paths.

### Scope

- Add package `packages/adeu_semantic_compiler` with compiler-core implementation for:
  - deterministic pass-manager orchestration,
  - deterministic typed commitments IR emission,
  - deterministic compiler diagnostics emission,
  - deterministic pass manifest emission for pass-order/replay evidence and per-pass hash chain-of-custody.
- Freeze compiler pass sequence and ordering in this arc:
  - `LoadCollection` -> `ValidateBlocks` -> `RevalidateNormalization` -> `BuildIR` -> `ResolveRefs` -> `TypecheckLocks`.
  - first-three passes are load/validate phases only and must not parse markdown source.
- Freeze compiler input boundary:
  - compiler input contract is `semantic_source_collection@0.1` (+ `semantic_source_diagnostics@0.1` for fail-closed handoff),
  - compiler core consumes normalized semantic-source artifacts only,
  - markdown parsing in compiler core is forbidden in this arc,
  - compiler core does not mutate v39 semantic-source contract shape in this arc,
  - input diagnostics handoff is binary: any v39 diagnostic `error` fails closed, and non-error diagnostics are carried forward deterministically into v40 diagnostics output,
  - no prose inference and no direct parser bypass paths are allowed in this arc.
- Freeze compiler output boundary:
  - output commitments IR contract target is `adeu_commitments_ir@0.1`,
  - compiler diagnostics contract is `semantic_compiler_diagnostics@0.1`,
  - pass manifest contract is `semantic_compiler_pass_manifest@0.1`,
  - commitments IR serialization ordering is deterministic: modules sort by `(module_kind, id)` and nested collections sort lexicographically by stable IDs,
  - pass manifest entries include `{name, index, input_sha256, output_sha256}` for deterministic chain-of-custody.
- Freeze diagnostics source-position policy:
  - compiler diagnostics positions are in source-path coordinate space (not normalized JSON line offsets),
  - `module_id` is sourced only from normalized semantic block declared metadata, with missing values kept as empty string and synthetic IDs forbidden,
  - line mapping uses source handoff coordinates when available and deterministic `start_line = 1` fallback when unavailable.
- Freeze contract-id equivalence:
  - `adeu_commitments_ir@0.1` maps to authoritative schema file `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json` in this arc.
- Freeze stdlib vocabulary posture:
  - compiler consumes frozen stdlib token families (`EffectTag`, `LockKind`, `AssertionType`, `EvidenceType`, `TrustLane`, `EvidenceQuality`),
  - `EvidenceQuality` maps to commitments IR type family `CommitmentsEvidenceQuality`,
  - unknown stdlib tokens fail closed.
- Freeze fail-closed core behavior:
  - unresolved references fail closed,
  - lock typecheck violations fail closed,
  - ambiguous module/lock bindings fail closed,
  - unknown compiler-level semantic tokens fail closed.
- Freeze pass hash-identity policy:
  - pass hash subject for `input_sha256`/`output_sha256` is canonical JSON bytes of pass input/output values,
  - mutating passes are fixed as `BuildIR` and `ResolveRefs`,
  - read-only passes (`LoadCollection`, `ValidateBlocks`, `RevalidateNormalization`, `TypecheckLocks`) may emit identical input/output hashes,
  - mutating passes emitting identical input/output hashes are invalid and fail closed.
- Keep v40 contract compiler-core only:
  - no surface snapshot/delta or PR/evidence codegen behavior is introduced in this arc,
  - no CI closeout wiring release is introduced in this arc.

### Locks

- Contract-surface lock is frozen:
  - v40 introduces compiler-core pass pipeline contract only.
- Entrypoint lock is frozen:
  - compile command authority is single-entrypoint (`python -m adeu_semantic_compiler.compile`); alternate entrypoints are non-authoritative.
- Pass-sequence lock is frozen:
  - pass sequence is exactly the frozen order in `v32c_compiler_core_contract@1`.
  - pass insertion/reordering/removal is out of scope in this arc.
  - first-three passes are load/validate-only phases and may not parse markdown source.
- Input-boundary lock is frozen:
  - compiler consumes only semantic-source normalized artifacts.
  - compiler does not mutate or reinterpret v39 semantic-source schema shape in this arc.
  - input diagnostics handoff is binary: any v39 diagnostic `error` fails closed and non-error diagnostics are carried forward deterministically.
  - parser re-interpretation and markdown parsing inside compiler core are forbidden in this arc.
- Output-contract lock is frozen:
  - compiler output artifacts are exactly `commitments_ir`, `semantic_compiler.diagnostics`, and `pass_manifest` under `artifacts/semantic_compiler/v40`.
  - commitments IR serialization ordering is deterministic: modules by `(module_kind, id)` and nested collections by stable-ID lexicographic order.
  - `pass_manifest` entries must include `{name, index, input_sha256, output_sha256}` for every pass.
  - writes outside this base directory are invalid and fail closed.
- Contract-id equivalence lock is frozen:
  - `adeu_commitments_ir@0.1` is equivalent to authoritative schema `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json` in this arc.
- Stdlib lock is frozen:
  - stdlib vocabulary version is `v32c_frozen_v1`.
  - unknown stdlib tokens are invalid and fail closed.
- Strictness lock is frozen:
  - unresolved references, lock type mismatches, and ambiguous bindings fail closed.
- Diagnostics lock is frozen:
  - diagnostics code namespace is `SCC[0-9]{4}`,
  - diagnostics ordering is deterministic by `(module_id, path, start_line, code)`,
  - `module_id` values are sourced from normalized semantic block declared metadata only (no synthetic IDs in v40),
  - diagnostics with missing `module_id` are serialized with `module_id = ""` for stable sort behavior,
  - diagnostics positions are emitted in source-path coordinate space with deterministic `start_line = 1` fallback when source mapping is unavailable,
  - normalized JSON line offsets are forbidden for diagnostics position reporting,
  - diagnostic line/column indexing is 1-based.
- Pass-manifest chain lock is frozen:
  - pass manifest is deterministic and includes per-pass input/output hashes for chain-of-custody replay evidence.
  - per-pass hash subject is canonical JSON bytes of pass input/output values.
- Pass-hash-identity lock is frozen:
  - mutating passes are exactly `BuildIR` and `ResolveRefs`,
  - `LoadCollection`, `ValidateBlocks`, `RevalidateNormalization`, and `TypecheckLocks` may emit equal input/output hashes,
  - equal input/output hashes on mutating passes are invalid and fail closed.
- Canonical-hash lock is frozen:
  - compiler artifacts use frozen canonical JSON hashing profile.
- No-runtime-mutation lock is frozen:
  - v40 may not modify runtime endpoint behavior/policy semantics.
- No-surface-governance-release lock is frozen:
  - v40 may not release `V32-D` surface snapshot/delta/codegen behavior.
- No-ci-gate-release lock is frozen:
  - v40 may not release `V32-E` CI/closeout integration behavior.
- No-metrics-expansion lock is frozen:
  - v40 may not introduce stop-gate metric-key changes.

### Acceptance

- Compiler-core pass pipeline MVP is present with deterministic commitments IR, diagnostics, and pass-manifest outputs.
- Compiler reruns under fixed semantic-source input are byte-identical for all v40 artifacts.
- No regression of v36/v37/v38/v39 continuity guards.

## O2) Compiler Core Determinism/Fail-Closed Guard Suite (`V32-C`)

### Goal

Prove compiler-core pass behavior is deterministic, fail-closed, and regression-resistant.

### Scope

- Add/adjust deterministic tests/guards for:
  - compiler rerun determinism (repeat runs yield byte-identical commitments IR, diagnostics, and pass-manifest outputs),
  - frozen pass-sequence assertions:
    - pass order matches locked sequence exactly,
    - first-three passes are `LoadCollection`, `ValidateBlocks`, `RevalidateNormalization` and do not parse markdown,
    - sequence drift fails closed,
  - strict stdlib vocabulary assertions:
    - unknown stdlib tokens fail closed,
    - lock/assertion token mismatches fail closed,
  - strict reference/typecheck assertions:
    - unresolved module references fail closed,
    - lock typecheck mismatches fail closed,
    - ambiguous bindings fail closed,
  - input diagnostics handoff assertions:
    - v39 diagnostics containing any `error` cause v40 fail-closed behavior,
    - v39 non-error diagnostics are carried into v40 diagnostics output deterministically,
  - deterministic diagnostics contract assertions:
    - diagnostic code namespace matches `SCC[0-9]{4}`,
    - diagnostics are byte-stable under `(module_id, path, start_line, code)` ordering,
    - `module_id` values are sourced from normalized semantic block declared metadata only (no synthetic IDs),
    - diagnostics with missing `module_id` are normalized to empty string for deterministic sort behavior,
    - diagnostics positions use source-path coordinates with deterministic fallback (`start_line = 1`) when mapping is unavailable,
    - normalized JSON line offsets are rejected as diagnostic position source,
    - diagnostic line/column numbering is 1-based,
  - commitments IR ordering assertions:
    - module ordering is deterministic by `(module_kind, id)`,
    - nested collections are deterministically sorted by stable-ID lexicographic order,
  - pass-manifest chain assertions:
    - pass manifest entries include `{name, index, input_sha256, output_sha256}` for every pass,
    - per-pass hashes are computed from canonical JSON bytes of pass input/output values,
    - per-pass input/output hash chain is deterministic across reruns,
  - pass-hash identity assertions:
    - read-only passes (`LoadCollection`, `ValidateBlocks`, `RevalidateNormalization`, `TypecheckLocks`) may produce equal input/output hashes,
    - mutating passes (`BuildIR`, `ResolveRefs`) are fixed and must not produce equal input/output hashes,
    - mutating passes producing equal input/output hashes fail closed,
  - generated-artifact cleanliness assertion:
    - rerun compiler entrypoint and fail closed if v40 artifacts differ from committed bytes,
  - continuity-preservation assertions:
    - v36/v37/v38/v39 continuity suites remain green and unreverted.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v40 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v39 continuity metrics remain at required values.
- Required-compiler-determinism lock is frozen:
  - v40 guards fail closed if compiler reruns drift by bytes.
- Required-fail-closed lock is frozen:
  - v40 guards fail closed if unresolved/type-invalid compiler inputs are silently accepted.
- Required-input-diagnostics-handoff lock is frozen:
  - v40 guards fail closed when v39 input diagnostics contain any `error` and fail closed if non-error carry-forward behavior drifts.
- Required-pass-order lock is frozen:
  - v40 guards fail closed if pass sequence order drifts from frozen contract.
- Required-ir-ordering lock is frozen:
  - v40 guards fail closed if commitments IR ordering drifts from deterministic `(module_kind, id)` and stable-ID lexicographic rules.
- Required-diagnostic-position-source lock is frozen:
  - v40 guards fail closed if diagnostics positions are sourced from normalized JSON offsets instead of source-path coordinate policy.
- Required-pass-manifest-chain lock is frozen:
  - v40 guards fail closed if pass-manifest entries, canonical-json hash subject, or per-pass input/output hash chain fields drift from frozen contract.
- Generated-artifact cleanliness lock is frozen:
  - v40 guards fail closed when deterministic compiler artifacts regenerate to non-committed deltas.
- Continuity-preservation lock is frozen:
  - v40 guards fail closed if v36/v37/v38/v39 continuity suites regress.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- CI lane continuity lock is frozen:
  - in-scope v40 compiler-core guards must run in default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required compiler determinism, pass-order freeze, and fail-closed assertions are green.
- Compiler-core strictness behavior is fail-closed and test-covered.
- v36/v37/v38/v39 continuity guard suites remain green under v40 scope.

## Stop-Gate Impact (v40)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v40 closeout must include runtime-observability comparison row against v39 baseline.
- v40 closeout must include compiler-core artifact evidence block:
  - block schema is docs-only `v32c_compiler_core_evidence@1`,
  - required keys are:
    - `schema`
    - `commitments_ir_artifact`
    - `diagnostics_artifact`
    - `pass_manifest_artifact`
    - `commitments_ir_sha256`
    - `diagnostics_sha256`
    - `pass_manifest_sha256`
    - `pass_manifest_chain_complete`
    - `byte_replay_equal`
    - `notes`
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
- Runtime-observability closeout placement lock is frozen:
  - v40 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS40.md` inside a machine-checkable JSON block.
- Runtime-observability interpretation lock is frozen:
  - v40 runtime-observability comparison row is required evidence and is informational-only for this arc,
  - no new pass/fail threshold is introduced in this arc on elapsed timing deltas.

## Error/Exit Policy (v40)

- No new URM error-code family is introduced in this arc.
- Semantic-compiler reason-code registry in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V32-C compiler core pass pipeline MVP`
2. `tests: add v40 compiler core determinism and fail-closed guard suite`

## Intermediate Preconditions (for v40 start)

1. v39 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v39 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md`
3. Existing semantic-source compiler front-end entrypoint remains available at v40 start:
   - `packages/adeu_semantic_source/src/adeu_semantic_source/compile.py`
4. Existing commitments IR contract remains available at v40 start:
   - `packages/adeu_commitments_ir/schema/adeu_commitments_ir.v0_1.json`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. Existing v31g persistence continuity lint remains enabled:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
7. No additional `L2` boundary release beyond v39 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `O1` and `O2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic compiler core pass pipeline MVP (`V32-C`) is closed and test-covered.
- v40 closeout evidence includes runtime-observability comparison row against v39 baseline.
- v36 governance, v37 persistence, v38 commitments, and v39 semantic-source continuity remain green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
