# Locked Continuation vNext+39 (Closed Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS38.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v6.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: closed lock (implemented on `main`, March 3, 2026 UTC).

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
- `vNext+39` (`N1`-`N2`) is now merged on `main` via PR `#224` and PR `#225` with green CI checks.
- `vNext+39` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS39.md` with `all_passed = true`.

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
  - baseline derived cardinality at v39 start is `79` and must remain unchanged in this arc,
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
  "export_call_pattern": "python -m adeu_semantic_source.compile",
  "semantic_source_allowlist_mode": "explicit_inputs_only",
  "input_interface": {
    "mode": "cli_explicit_paths",
    "accepts": [
      "--input",
      "--inputs_manifest"
    ],
    "duplicates": "error",
    "must_be_under_root": true,
    "manifest_entry_resolution": "relative_to_manifest_dir",
    "manifest_absolute_paths": "forbidden",
    "manifest_ordering": "preserve_file_order"
  },
  "semantic_frontmatter_enabled": true,
  "frontmatter_yaml_profile": {
    "spec": "yaml_1_2",
    "structure": "mapping_only",
    "forbidden_features": [
      "anchors",
      "aliases",
      "tags"
    ]
  },
  "frontmatter_semantic_key_policy": "prefix_allowlist",
  "frontmatter_semantic_key_prefixes": [
    "adeu_",
    "asc_"
  ],
  "frontmatter_unknown_semantic_keys": "error",
  "semantic_fence_label_pattern": "^adeu(\\..+)?$",
  "fence_style": "triple_backtick_only",
  "content_normalization": {
    "line_endings": "lf",
    "trim_trailing_whitespace": true,
    "preserve_internal_whitespace": true
  },
  "prose_semantic_authority": "forbidden",
  "normalized_schema_contract_id": "semantic_source_collection@0.1",
  "normalized_output_artifact": "artifacts/semantic_compiler/v39/semantic_source.normalized.json",
  "diagnostics_output_artifact": "artifacts/semantic_compiler/v39/semantic_source.diagnostics.json",
  "output_path_policy": {
    "relative_to_repo_root": true,
    "base_dir": "artifacts/semantic_compiler/v39",
    "auto_create_directories": true,
    "allow_outside_base_dir": false
  },
  "path_normalization": {
    "separator": "posix",
    "collapse_dot_segments": true,
    "resolve_symlinks": false,
    "root_boundary_check": "lexical_after_normalization"
  },
  "diagnostic_code_namespace": "SSC",
  "diagnostic_code_pattern": "^SSC[0-9]{4}$",
  "diagnostic_sort_order": [
    "path",
    "start_line",
    "code"
  ],
  "diagnostic_position_base": {
    "line": 1,
    "column": 1
  },
  "duplicate_identifier_diagnostic_payload": "all_claim_sites",
  "semantic_source_collection_contract_publication": "internal_label_only_schema_publication_deferred",
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
  - single authoritative compile entrypoint (`python -m adeu_semantic_source.compile`) for contract-authoritative output generation,
  - explicit input interface (`--input` and `--inputs_manifest`) as the only source selection mechanism in this arc,
  - optional YAML frontmatter handling,
  - fenced semantic blocks labeled `adeu` or `adeu.*`,
  - deterministic source discovery from explicit inputs,
  - deterministic normalized semantic-source payload output,
  - deterministic diagnostics output with stable reason codes.
- Freeze semantic-input interface:
  - input set must come only from explicit CLI args or an explicit inputs manifest file.
  - duplicate input entries fail closed.
  - input paths outside declared docs root fail closed.
  - manifest entry paths resolve relative to the manifest file directory.
  - absolute paths in manifest entries are forbidden and fail closed.
  - manifest file order is authoritative and preserved for parser input ordering.
  - v39 parser invocation is not a repo-wide scan mode; implicit discovery is forbidden by contract.
- Freeze semantic-authority boundary:
  - semantic authority derives only from explicit semantic blocks.
  - prose inference is forbidden.
- Freeze frontmatter YAML profile:
  - frontmatter is parsed as YAML 1.2 mapping-only payloads.
  - anchors, aliases, and tags are rejected (fail closed).
- Freeze frontmatter semantic-key policy:
  - only `adeu_` and `asc_` prefixed frontmatter keys are semantic-authoritative.
  - non-prefixed frontmatter keys are non-authoritative metadata in this arc.
  - unknown semantic-prefixed keys fail closed.
- Freeze fence and content normalization rules:
  - only triple-backtick semantic fences are supported.
  - indented and tilde fences are rejected (fail closed).
  - content normalization uses LF line endings, trims trailing whitespace, and preserves internal whitespace.
- Freeze fail-closed parse posture:
  - malformed frontmatter/blocks fail closed,
  - unknown semantic block labels fail closed,
  - duplicate module identifiers fail closed,
  - ambiguous semantic declarations fail closed.
- Freeze diagnostics contract:
  - diagnostics reason-code namespace uses `SSC[0-9]{4}` in this arc.
  - diagnostics ordering is deterministic by `(path, start_line, code)`.
  - diagnostic line/column numbering is 1-based.
  - duplicate-identifier diagnostics include all collision participants as `(path, start_line)` claim sites.
- Freeze output-path contract:
  - semantic-source outputs are written only under `artifacts/semantic_compiler/v39`.
  - writes outside that base directory are invalid and fail closed.
- Freeze path-normalization contract:
  - path canonicalization uses POSIX separators.
  - dot segments are collapsed deterministically.
  - symlink resolution is not used for canonicalization in this arc.
  - docs-root boundary checks are lexical after normalization and do not depend on symlink resolution.
- Keep v39 contract parser-only:
  - no compiler pass-manager assumptions are embedded into required v0 semantic-source fields.

### Locks

- Contract-surface lock is frozen:
  - v39 introduces semantic-source parser/normalizer contract only.
  - compile command authority is single-entrypoint (`python -m adeu_semantic_source.compile`); alternate entrypoints are non-authoritative.
- Semantic-authority lock is frozen:
  - only explicit semantic blocks influence normalized semantic outputs.
- Discovery lock is frozen:
  - parser input set is explicit and deterministic; implicit repo-wide discovery is forbidden in this arc.
  - input set must come only from explicit CLI args or an explicit manifest file; implicit traversal is a hard error.
  - parser is intentionally non-scanning in v39; bulk input selection belongs to an explicit follow-on scope.
  - manifest entry paths are resolved relative to manifest directory and processed in manifest file order.
  - absolute paths in manifest entries are forbidden.
- Grammar lock is frozen:
  - v39 supports YAML frontmatter and fenced `adeu` blocks only.
  - only triple-backtick semantic fences are allowed; indented and tilde fences are invalid and fail closed.
- Frontmatter-YAML lock is frozen:
  - frontmatter parsing is YAML 1.2 mapping-only.
  - anchors, aliases, and tags are invalid and fail closed.
- Frontmatter-key policy lock is frozen:
  - only `adeu_` and `asc_` prefixed frontmatter keys are semantic-authoritative.
  - unknown semantic-prefixed keys fail closed.
  - non-prefixed frontmatter keys are non-authoritative and excluded from semantic hash derivation.
- Strictness lock is frozen:
  - unknown or malformed semantic blocks fail closed.
- Deterministic-normalization lock is frozen:
  - normalized outputs and diagnostics are deterministic and stable across reruns.
  - line ending normalization is LF-only; trailing whitespace is trimmed while internal whitespace is preserved.
- Diagnostics-contract lock is frozen:
  - diagnostics codes must match `SSC[0-9]{4}`.
  - diagnostics sort order is `(path, start_line, code)`.
  - diagnostic line/column indexing is 1-based.
  - duplicate-identifier diagnostics must enumerate all collision claim sites `(path, start_line)`.
- Output-path lock is frozen:
  - normalized and diagnostics artifacts must be emitted under `artifacts/semantic_compiler/v39` only.
  - output writes outside that base directory fail closed.
- Path-normalization lock is frozen:
  - canonicalized path separator is POSIX.
  - dot-segment collapsing is deterministic.
  - canonicalization does not depend on symlink resolution.
  - root-boundary enforcement is lexical after path normalization.
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
  - explicit-input interface assertions:
    - only `--input` and `--inputs_manifest` are accepted input mechanisms,
    - duplicate explicit inputs fail closed,
    - out-of-root input paths fail closed,
    - manifest entries resolve relative to manifest directory,
    - manifest absolute paths fail closed,
    - manifest file order is preserved as authoritative input order,
  - deterministic source ordering assertions,
  - fence-style assertions:
    - triple-backtick semantic fences are accepted,
    - indented/tilde fences are rejected fail closed,
  - frontmatter YAML-profile assertions:
    - YAML 1.2 mapping-only frontmatter is accepted,
    - anchors/aliases/tags are rejected fail closed,
  - frontmatter semantic-key policy assertions:
    - only `adeu_` / `asc_` prefixed keys are semantic-authoritative,
    - unknown semantic-prefixed keys fail closed,
  - strict unknown/malformed semantic block rejection assertions,
  - strict duplicate/ambiguous semantic declaration rejection assertions,
  - normalization assertions:
    - line endings normalize to LF,
    - trailing whitespace is trimmed without collapsing internal whitespace,
  - path canonicalization assertions:
    - normalized paths use POSIX separators,
    - dot segments are collapsed deterministically,
    - canonicalization does not resolve symlinks,
    - root-boundary checks are lexical after normalization,
  - diagnostic contract assertions:
    - diagnostic code namespace matches `SSC[0-9]{4}`,
    - diagnostics are byte-stable under `(path, start_line, code)` ordering,
    - diagnostic line/column numbering is 1-based,
    - duplicate-identifier diagnostics include all claim-site participants `(path, start_line)`,
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
- Schema export/mirror for semantic-source artifacts is not part of v39 scope and requires explicit follow-on lock text if introduced.
- `semantic_source_collection@0.1` is an internal contract label in v39; JSON schema publication is deferred and requires explicit follow-on lock text.
