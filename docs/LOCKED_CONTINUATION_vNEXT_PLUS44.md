# Locked Continuation vNext+44 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS43.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet).

## Draft-State Marker (Machine-Checkable)

```json
{
  "schema": "lock_artifact_state@1",
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS44.md",
  "phase": "draft_lock",
  "authoritative": false,
  "authoritative_scope": "planning_intent_only",
  "required_in_freeze_review": true,
  "required_in_closeout": true,
  "notes": "Draft lock placeholder state. Freeze-review and closeout updates must promote this artifact from planning-intent-only posture."
}
```

Decision basis:

- `vNext+43` (`V32-F`) is merged on `main` via PR `#233` with green CI checks.
- `vNext+43` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS43.md`.
- Post-v43 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`.
- Selected v44 thin-slice default is agent harness contract/compiler candidate:
  - `V33-A` (Pipeline Profile + TaskPack contracts + deterministic compiler).
- `vNext+44` is constrained to deterministic additive hardening for `V33-A` only:
  - no Codex SDK execution runner release (`V33-B`) in this arc,
  - no verifier/evidence writer lane release (`V33-C`) in this arc,
  - no integrated/standalone UX packaging release (`V33-D`) in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v44,
  - v44 keyset must be exactly equal to v43 keyset (set equality),
  - derived metric-key cardinality baseline at v44 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36-v43 continuity guarantees remain frozen as release preconditions:
  - v36 governance continuity remains authoritative,
  - v37 persistence continuity remains authoritative,
  - v38 commitments IR continuity remains authoritative,
  - v39 semantic-source continuity remains authoritative,
  - v40 compiler-core continuity remains authoritative,
  - v41 surface-governance continuity remains authoritative,
  - v42 CI/closeout wiring continuity remains authoritative,
  - v43 additive key-migration continuity remains authoritative.
- Boundary-release scope lock for v44 is frozen:
  - this arc authorizes no `L2` boundary release.
- ASC semantic interpretation boundary lock is frozen:
  - semantic authority for harness compilation derives from compiled ASC artifacts and explicit profile contracts only,
  - narrative prose is non-authoritative for taskpack semantic authority.
- Pipeline-profile resolution lock is frozen:
  - profile selection key is stable `profile_id`,
  - profile resolution authority is `registry_only`,
  - profile resolution semantics are deterministic and pure,
  - ad-hoc local profile path ingestion is forbidden.
- Pipeline-profile registry hash-binding lock is frozen:
  - registry entries must bind `profile_id` to a declared canonical profile hash,
  - compiler must recompute canonical profile hash for resolved profile payload,
  - resolved profile hash mismatch against registry-declared hash is invalid and fails closed.
- Pipeline-profile registry representation lock is frozen:
  - registry contract schema is docs-authoritative `taskpack_profile_registry@1`,
  - registry payload is canonical JSON object content (no imperative/dynamic source-of-truth),
  - each registry entry requires `profile_id`, `profile_sha256`, and `profile_payload_path`,
  - `profile_id` values must be unique and deterministically sorted for canonical serialization.
- Semantic-compiler authority input version-selection lock is frozen:
  - authority-input glob patterns denote artifact-family scope only in lock prose,
  - compiler resolution is by explicit single `source_semantic_arc` selection,
  - selected arc resolves to exact artifact paths only,
  - zero-match or multi-match arc resolution is invalid and fails closed.
- TaskPack ABI integrity lock is frozen:
  - component schema IDs are authoritative only via `taskpack_manifest.json`,
  - component schema ID format is `taskpack/<component>@<version>`,
  - bundle hash subject is canonical JSON hash of `taskpack_manifest.json` only.
- TaskPack markdown projection lock is frozen:
  - canonical markdown profile is required (`UTF-8`, `LF`, frozen section order, deterministic whitespace policy),
  - machine-readable attribution markers are required (`<!-- adeu:... -->`),
  - attribution markers must include `source_schema_id` and `source_component_hash` and be verifier-checkable.
- Attribution marker collision lock is frozen:
  - marker-like user payload text cannot satisfy attribution authority,
  - renderer-owned marker positions are frozen to semantic-section EOF marker lines at root markdown scope,
  - marker-like text inside code fences, blockquotes, or non-owned positions is non-authoritative,
  - verifier authority is limited to renderer-owned semantic-section marker positions,
  - marker collision or spoofing detection is fail-closed.
- Closeout observability continuity lock is frozen:
  - v44 closeout must include a runtime-observability comparison row against v43 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `S1` Pipeline Profile + TaskPack contracts + deterministic compiler MVP (`V33-A`)
2. `S2` Determinism/fail-closed guard suite for `V33-A`

Out-of-scope note:

- Codex SDK constrained runner execution surface (`V33-B`) in this arc,
- auditor/verifier/evidence-writer lane (`V33-C`) in this arc,
- integrated + standalone UX packaging (`V33-D`) in this arc,
- delta-aware taskpack recompilation/caching optimizations in this arc,
- cryptographic signing of taskpack bundle hash in this arc,
- stop-gate metric-key expansion in this arc,
- schema-family fork in this arc,
- runtime/provider/proposer boundary release changes in this arc.

## V43 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md",
  "target": "V33-A",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN",
    "V32_C_COMPILER_CORE_CONTINUITY_GREEN",
    "V32_D_SURFACE_CODEGEN_CONTINUITY_GREEN",
    "V32_E_CI_CLOSEOUT_CONTINUITY_GREEN",
    "V32_F_METRIC_EXTENSION_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v44.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V33-A TaskPack Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v33a_taskpack_contract@1",
  "target_arc": "vNext+44",
  "target_path": "V33-A",
  "authority_inputs": {
    "semantic_compiler_evidence_manifest": "artifacts/semantic_compiler/*/evidence_manifest.json",
    "semantic_compiler_surface_diff": "artifacts/semantic_compiler/*/surface_diff.json",
    "compiled_commitments_ir_artifacts": "required",
    "pipeline_profile_contract": "required"
  },
  "semantic_compiler_input_resolution": {
    "source_semantic_arc": "required_single_arc_id",
    "resolution_policy": "exact_paths_for_selected_arc_only",
    "glob_role": "family_scope_descriptor_only",
    "zero_or_multi_arc_match": "fail_closed"
  },
  "raw_docs_as_semantic_input_for_taskpack_compiler": false,
  "profile_resolution": {
    "key": "profile_id",
    "authority": "registry_only",
    "ad_hoc_profile_path_input": "forbidden",
    "resolution_semantics": "deterministic_pure_resolution",
    "registry_declared_profile_hash": "required_sha256_canonical_json",
    "resolved_profile_hash_verification": "required_exact_match_fail_closed",
    "registry_contract_schema": "taskpack_profile_registry@1",
    "registry_entry_required_fields": [
      "profile_id",
      "profile_sha256",
      "profile_payload_path"
    ],
    "registry_profile_id_uniqueness": "required"
  },
  "taskpack_components": {
    "required": [
      "TASKPACK.md",
      "ACCEPTANCE.json",
      "ALLOWLIST.json",
      "FORBIDDEN.json",
      "COMMANDS.json",
      "EVIDENCE_SLOTS.json",
      "taskpack_manifest.json"
    ],
    "component_schema_id_format": "taskpack/<component>@<version>",
    "bundle_hash_subject": "sha256_canonical_json(taskpack_manifest.json)",
    "taskpack_manifest_authority": "component_schema_ids_and_component_hashes"
  },
  "markdown_projection_policy": {
    "encoding": "utf-8",
    "line_endings": "lf",
    "section_order": "frozen",
    "required_section_order_ids": [
      "taskpack_header",
      "task_scope",
      "acceptance",
      "allowlist",
      "forbidden",
      "commands",
      "evidence_slots",
      "attribution"
    ],
    "deterministic_whitespace": "required",
    "attribution_marker_syntax": "<!-- adeu:... -->",
    "required_attribution_fields": [
      "source_schema_id",
      "source_component_hash"
    ],
    "attribution_verifier": "required",
    "attribution_verifier_scope": "renderer_owned_semantic_section_markers_only",
    "attribution_marker_position_rule": "exactly_one_root_scope_eof_marker_per_semantic_section",
    "markdown_parser_scope": "root_scope_excluding_code_fence_and_blockquote_content",
    "marker_collision_policy": "spoof_or_collision_detected_fail_closed",
    "marker_like_text_in_non_authoritative_content": "ignored_non_authoritative"
  },
  "deterministic_env": {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0"
  },
  "fail_closed_conditions": [
    "authority_input_missing",
    "authority_input_schema_mismatch",
    "authority_input_version_selection_ambiguous",
    "profile_resolution_failure",
    "ad_hoc_profile_path_input_detected",
    "profile_registry_entry_missing_or_malformed",
    "profile_registry_schema_mismatch",
    "profile_registry_duplicate_profile_id",
    "profile_registry_hash_mismatch",
    "taskpack_component_missing",
    "taskpack_component_schema_id_drift",
    "taskpack_manifest_component_hash_mismatch",
    "taskpack_bundle_hash_subject_drift",
    "markdown_projection_nondeterminism",
    "markdown_projection_section_order_drift",
    "markdown_attribution_marker_missing",
    "markdown_attribution_marker_position_invalid",
    "markdown_attribution_verifier_failure",
    "markdown_attribution_marker_collision_detected",
    "markdown_attribution_marker_spoof_detected",
    "required_violation_reported_as_warning"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## S1) Pipeline Profile + TaskPack Contracts + Deterministic Compiler MVP (`V33-A`)

### Goal

Introduce deterministic contract surfaces and compiler outputs for taskpack generation from authoritative ASC artifacts and profile contracts.

### Scope

- Add typed Pipeline Profile schema surface and strict validation.
- Add deterministic registry hash-binding for profile resolution:
  - registry binds `profile_id` to declared canonical profile hash,
  - compiler fails closed on resolved profile hash mismatch.
- Add deterministic profile-registry contract enforcement:
  - registry schema is `taskpack_profile_registry@1` with strict required fields and unique `profile_id`.
- Add deterministic semantic-compiler authority-input resolution:
  - compiler selects one explicit `source_semantic_arc`,
  - selected arc resolves to exact authority paths and fails closed on zero/multi-match ambiguity.
- Add a portable harness-kernel package boundary (for example `packages/adeu_agent_harness`) that owns profile/taskpack schemas and deterministic compiler/serialization primitives.
- Add typed TaskPack component schemas and authoritative `taskpack_manifest.json`.
- Add deterministic compiler entrypoint that emits:
  - `TASKPACK.md`
  - `ACCEPTANCE.json`
  - `ALLOWLIST.json`
  - `FORBIDDEN.json`
  - `COMMANDS.json`
  - `EVIDENCE_SLOTS.json`
  - `taskpack_manifest.json`
- Add deterministic manifest/hash verification and projection-attribution emission.
- Add deterministic attribution-marker collision protection:
  - marker-like payload text in non-authoritative content cannot satisfy attribution checks,
  - verifier accepts only renderer-owned semantic-section marker positions.
- Add deterministic markdown projection section-order enforcement with frozen section-order IDs.
- Add deterministic diagnostics for fail-closed contract violations.

### Locks

- Profile-authority lock:
  - profile resolution is by authoritative `profile_id` only.
- Profile-registry hash-binding lock:
  - profile registry resolution includes declared canonical profile hash and strict resolved-hash verification.
- Profile-registry contract lock:
  - registry schema/fields/uniqueness are strictly validated and fail closed on drift.
- Compiler-authority lock:
  - compiler input authority is compiled ASC artifacts plus profile contract only.
- Authority-input version-selection lock:
  - compiler resolves authority inputs from exactly one explicit semantic arc and rejects ambiguous glob-based resolution.
- ABI lock:
  - component schema IDs and component hashes are authoritative via manifest only.
- Projection lock:
  - markdown projection obeys canonical profile and frozen attribution markers.
- Attribution-collision lock:
  - marker spoofing/collision is rejected fail-closed under frozen verifier scope.
- Markdown section-order lock:
  - `TASKPACK.md` section-order IDs are frozen and fail closed on drift.
- Severity lock:
  - required contract violations are errors and fail closed.

### Acceptance

- Taskpack bundle artifacts are byte-identical across reruns with fixed inputs.
- Manifest component-hash verification is deterministic and fail-closed.
- Markdown attribution verifier passes deterministically on valid outputs and fails closed on missing/invalid markers.
- Profile registry hash-binding verification passes deterministically and fails closed on mismatch.
- Profile-registry schema/uniqueness verification passes deterministically and fails closed on drift.
- Semantic-compiler authority input resolution passes deterministically for one explicit source arc and fails closed on ambiguous arc selection.

## S2) Determinism-Fail-Closed Guard Suite (`V33-A`)

### Goal

Prove v44 contract/compiler behavior is deterministic, fail-closed, and continuity-preserving.

### Scope

- Add/adjust deterministic tests/guards for:
  - profile schema validation failures,
  - registry-only profile resolution enforcement,
  - ad-hoc profile path rejection,
  - profile registry schema mismatch and duplicate `profile_id` failures,
  - profile registry entry malformed/missing failures,
  - resolved profile hash mismatch against registry-declared hash failures,
  - semantic-compiler authority input version-selection ambiguity failures (zero/multi arc match),
  - authority input missing/schema drift failures,
  - taskpack component missing failures,
  - component schema-id format drift failures,
  - manifest component-hash mismatch failures,
  - bundle-hash subject drift failures,
  - markdown projection determinism across reruns,
  - markdown section-order ID drift failures,
  - attribution marker presence and parser/verifier failures,
  - attribution marker position-rule violations at root scope,
  - attribution marker collision/spoof detection failures (including marker-like text in non-authoritative content),
  - required error-channel enforcement (no warning downgrade for required violations),
  - continuity-preservation assertions for v36-v43 frozen suites.

### Locks

- No-new-metric-keys lock is frozen:
  - v44 tests/guards may not introduce new stop-gate metric keys.
- Required-deterministic-env lock is frozen:
  - `TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`.
- Required-severity-policy lock is frozen:
  - required violations are errors and fail closed.
- Continuity-preservation lock is frozen:
  - v36-v43 continuity suites remain required and green.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required contract wiring and fail-closed assertions are green.
- v36-v43 continuity guard suites remain green under v44 scope.

## Stop-Gate Impact (v44)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- v44 closeout must include runtime-observability comparison row against v43 baseline.
- v44 closeout must include taskpack wiring evidence block:
  - block schema is docs-only `v33a_taskpack_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `taskpack_compiler_entrypoint`
    - `profile_registry_source`
    - `authority_inputs_verified`
    - `taskpack_manifest_hash`
    - `taskpack_bundle_hash_matches_manifest`
    - `markdown_projection_deterministic`
    - `attribution_verifier_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v43`
    - `notes`

## Error/Exit Policy (v44)

- No new URM runtime error-code family is introduced in this arc.
- Harness diagnostics namespace (`AHK[0-9]{4}`) in this arc is contract-diagnostics authority only.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V33-A pipeline profile and taskpack contract/compiler MVP`
2. `tests: add v44 taskpack determinism and fail-closed guard suite`

## Intermediate Preconditions (for v44 start)

1. v43 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v43 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS43.md`
3. ASC compiled artifact surfaces required for taskpack authority remain available.
4. Existing stop-gate continuity tooling remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
5. No additional `L2` boundary release beyond v43 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `S1` and `S2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic `V33-A` taskpack contract/compiler MVP is closed and test-covered.
- v44 closeout evidence includes runtime-observability comparison row against v43 baseline.
- v36-v43 continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
