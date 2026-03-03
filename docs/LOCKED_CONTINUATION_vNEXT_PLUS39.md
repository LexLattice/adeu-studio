# Locked Continuation vNext+39 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet).

Decision basis:

- `vNext+38` (`M1`-`M2`) is merged on `main` via PR `#222` and PR `#223` with green CI checks.
- `vNext+38` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md` with `all_passed = true`.
- Post-v38 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`.
- Selected v39 thin-slice default is semantic-source compiler front-end candidate:
  - `V32-B` (semantic source grammar/parser/normalizer MVP).
- `vNext+39` is constrained to deterministic additive hardening for `V32-B` only:
  - no solver/runtime semantics release,
  - no governance/persistence boundary release expansion,
  - no compiler pass-manager release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v39,
  - v39 keyset must be exactly equal to v38 keyset (set equality, derived cardinality),
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
- Boundary-release scope lock for v39 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for ASC-path work derives only from explicit semantic blocks,
  - narrative prose is non-authoritative for semantic hash derivation,
  - prose-inference parsing is forbidden unless explicitly authorized by a future lock.
- Closeout observability continuity lock is frozen:
  - v39 closeout must include a runtime-observability comparison row against v38 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `N1` semantic source grammar/parser/normalizer MVP (`V32-B`)
2. `N2` semantic source determinism/fail-closed guard suite (`V32-B`)

Out-of-scope note:

- any `SEMANTICS_v4` runtime contract release,
- commitments IR schema evolution release (`V32-A`) in this arc,
- compiler pass-manager release (`V32-C`) in this arc,
- surface snapshot/delta/codegen release (`V32-D`) in this arc,
- semantic-compiler CI gate integration release (`V32-E`) in this arc,
- stop-gate metric-key expansion for semantic compiler evidence (`V32-F`) in this arc,
- any provider or proposer endpoint expansion,
- new stop-gate metric keys or schema-family forks.

## Deferred Follow-on Candidates (Non-v39)

- v40+ compiler core pass pipeline (`V32-C`).
- v41+ surface snapshot/delta + PR/evidence codegen (`V32-D`).
- v42+ CI/closeout evidence wiring (`V32-E`) and optional stop-gate metric extension (`V32-F`) via explicit lock update.

## V38 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md",
  "target": "V32-B",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v39.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V32-B Semantic Source Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v32b_semantic_source_contract@1",
  "source_docs_root": "docs",
  "semantic_source_allowlist_mode": "explicit_inputs_only",
  "semantic_frontmatter_enabled": true,
  "semantic_fence_label_pattern": "^adeu(\\..+)?$",
  "prose_semantic_authority": "forbidden",
  "normalized_schema_contract_id": "semantic_source_collection@0.1",
  "normalized_output_artifact": "artifacts/semantic_compiler/v39/semantic_source.normalized.json",
  "diagnostics_output_artifact": "artifacts/semantic_compiler/v39/semantic_source.diagnostics.json",
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## N1) Semantic Source Grammar/Parser/Normalizer MVP (`V32-B`)

### Goal

Introduce deterministic semantic-source extraction and normalization from explicit semantic blocks only.

Lock-class rationale:

- this slice is `L1` because it introduces a new deterministic semantic-source contract surface and normalized artifact contract for follow-on compiler passes.

### Scope

- Add semantic-source grammar contract and parser/normalizer implementation with:
  - optional YAML frontmatter handling,
  - fenced semantic blocks labeled `adeu` or `adeu.*`,
  - deterministic source discovery from explicit inputs,
  - deterministic normalized semantic-source payload output,
  - deterministic diagnostics output with stable reason codes.
- Freeze semantic-authority boundary:
  - semantic authority derives only from explicit semantic blocks.
  - prose inference is forbidden.
- Freeze fail-closed parse posture:
  - malformed frontmatter/blocks fail closed,
  - unknown semantic block labels fail closed,
  - duplicate module identifiers fail closed,
  - ambiguous semantic declarations fail closed.
- Keep v39 contract parser-only:
  - no compiler pass-manager assumptions are embedded into required v0 semantic-source fields.

### Locks

- Contract-surface lock is frozen:
  - v39 introduces semantic-source parser/normalizer contract only.
- Semantic-authority lock is frozen:
  - only explicit semantic blocks influence normalized semantic outputs.
- Discovery lock is frozen:
  - parser input set is explicit and deterministic; implicit repo-wide discovery is forbidden in this arc.
- Grammar lock is frozen:
  - v39 supports YAML frontmatter and fenced `adeu` blocks only.
- Strictness lock is frozen:
  - unknown or malformed semantic blocks fail closed.
- Deterministic-normalization lock is frozen:
  - normalized outputs and diagnostics are deterministic and stable across reruns.
- Canonical-hash lock is frozen:
  - semantic-source hash assertions use frozen canonical JSON hashing profile.
- No-runtime-mutation lock is frozen:
  - v39 may not modify runtime endpoint behavior/policy semantics.
- No-pass-manager-release lock is frozen:
  - v39 may not release compiler pass-manager behavior (`V32-C`).
- No-metrics-expansion lock is frozen:
  - v39 may not introduce stop-gate metric-key changes.

### Acceptance

- Semantic-source parser/normalizer MVP is present and deterministic for fixed inputs.
- Normalized output and diagnostics artifacts are reproducible by bytes for repeated runs.
- No regression of v36/v37/v38 continuity guards.

## N2) Semantic Source Determinism/Fail-Closed Guard Suite (`V32-B`)

### Goal

Prove semantic-source parser/normalizer behavior is deterministic, fail-closed, and regression-resistant.

### Scope

- Add/adjust deterministic tests/guards for:
  - parser/normalizer rerun determinism (repeat runs yield byte-identical normalized payload and diagnostics),
  - deterministic source ordering assertions,
  - strict unknown/malformed semantic block rejection assertions,
  - strict duplicate/ambiguous semantic declaration rejection assertions,
  - prose-non-authority assertions (prose-only edits do not alter semantic output hash),
  - stable schema/version label assertions for semantic-source contract artifacts,
  - generated-artifact cleanliness assertion for deterministic semantic-source outputs.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC` and `LC_ALL=C` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v39 tests/guards may not introduce new stop-gate metric keys.
- Historical-continuity lock is frozen:
  - existing v38 continuity metrics remain at required values.
- Required-parser-determinism lock is frozen:
  - v39 guards fail closed if parser/normalizer reruns drift by bytes.
- Required-fail-closed lock is frozen:
  - v39 guards fail closed if malformed/unknown semantic inputs are silently accepted.
- Prose-non-authority lock is frozen:
  - v39 guards fail closed if prose-only edits alter normalized semantic outputs.
- Generated-artifact cleanliness lock is frozen:
  - v39 guards fail closed when deterministic semantic-source artifacts regenerate to non-committed deltas.
- Continuity-preservation lock is frozen:
  - v39 guards fail closed if v36/v37/v38 continuity suites regress.
- Deterministic-guard-output lock is frozen:
  - guard outputs are deterministic and machine-checkable under fixed inputs.
- CI lane continuity lock is frozen:
  - in-scope v39 parser guards must run in default Python CI lane,
  - workflow/job renaming is allowed only if required guard coverage remains equivalent and explicit in CI config.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required parser determinism and fail-closed assertions are green.
- Semantic-source strictness behavior is fail-closed and test-covered.
- v36/v37/v38 continuity guard suites remain green under v39 scope.

## Stop-Gate Impact (v39)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v39 closeout must include runtime-observability comparison row against v38 baseline.
- v39 closeout must include semantic-source artifact evidence block:
  - block schema is docs-only `v32b_semantic_source_evidence@1`,
  - required keys are:
    - `schema`
    - `normalized_output_artifact`
    - `diagnostics_output_artifact`
    - `normalized_sha256`
    - `diagnostics_sha256`
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
  - v39 comparison row must be emitted in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md` inside a machine-checkable JSON block.
- Runtime-observability interpretation lock is frozen:
  - v39 runtime-observability comparison row is required evidence and is informational-only for this arc,
  - no new pass/fail threshold is introduced in this arc on elapsed timing deltas.

## Error/Exit Policy (v39)

- No new URM error-code family is introduced in this arc.
- Semantic-source parser reason-code registry in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V32-B semantic-source grammar/parser/normalizer MVP`
2. `tests: add v39 semantic-source determinism and fail-closed guard suite`

## Intermediate Preconditions (for v39 start)

1. v38 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v38 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md`
3. Existing schema-export authority pattern remains available at v39 start:
   - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
4. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
5. Existing v31g persistence continuity lint remains enabled:
   - `apps/api/scripts/lint_v31g_persistence_release.py`
6. No additional `L2` boundary release beyond v38 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `N1` and `N2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic semantic-source grammar/parser/normalizer MVP (`V32-B`) is closed and test-covered.
- v39 closeout evidence includes runtime-observability comparison row against v38 baseline.
- v36 governance, v37 persistence, and v38 commitments continuity remain green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
