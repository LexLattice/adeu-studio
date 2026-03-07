# Locked Continuation vNext+54 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS53.md`
- `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 7, 2026 UTC).

## Decision Basis

- `vNext+53` (`V34-E`, `B1`/`B2`) is merged on `main` with green CI checks.
- `vNext+53` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS53.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md` marks the provider-neutral `V34-E` attested
  verifier-ingestion baseline as closed and restores eligibility for explicit `V34-F`
  evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-F` as the next deferred family candidate
  after the current trust and attestation lanes.
- current harness reality is narrower than a full standalone portability lane:
  - packaging is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`,
  - packaging manifests already emit deterministic `packaging_bundle_hash` over manifest
    inventory rows,
  - standalone packaging output already exists and is parity-constrained on `main`,
  - no released `standalone_integrity_verification_result@1` artifact exists on `main`,
  - no shared standalone integrity checker exists on `main`,
  - no released standalone self-verification CLI or evidence contract exists on `main`.
- `vNext+54` therefore selects one thin `V34-F` baseline slice only:
  - shared deterministic standalone bundle integrity checker over the current standalone
    packaging manifest inventory and emitted bundle files,
  - deterministic `standalone_integrity_verification_result@1`,
  - canonical closeout evidence integration plus guard coverage,
  - no installer/updater integration, archive fetch/unpack, or deployment-mode expansion in
    this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v54,
  - v54 keyset must be exactly equal to v53 keyset,
  - baseline derived cardinality at v54 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v54 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no governance or persistence authority release is authorized in this arc,
  - no remote execution transport, remote job dispatch, or deployment-mode release is
    authorized in this arc.
- `V34-A` signing and downstream-handoff completion remain frozen prerequisites:
  - signing subject remains `taskpack_bundle_hash`,
  - downstream runner/verifier/packaging consumption remains required and unchanged,
  - `v34a_handoff_completion_evidence@1` remains part of the canonical closeout surface.
- `V34-B` matrix baseline remains a frozen prerequisite:
  - declared matrix-lane registry/report contracts remain unchanged,
  - current released matrix parity evidence remains unchanged,
  - no adapter-kind or multi-runtime expansion is authorized in this arc.
- `V34-C` verifier-lane policy-recompute baseline remains a frozen prerequisite:
  - recompute comparison subject and fail-closed verifier behavior remain unchanged,
  - `policy_recompute_result@1` and `v34c_policy_recompute_evidence@1` remain part of the
    canonical closeout surface.
- `V34-D` retry-context baseline remains a frozen prerequisite:
  - advisory retry-context feeder contracts remain unchanged,
  - `retry_context_feeder_result@1`, `retry_context_sanitization_profile@1`, and
    `v34d_retry_context_evidence@1` remain part of the canonical closeout surface.
- `V34-E` attestation baseline remains a frozen prerequisite:
  - provider-neutral attestation normalization and exact local-equivalence requirements
    remain unchanged,
  - `remote_enclave_attestation@1`, `attestation_verification_result@1`, and
    `v34e_attestation_evidence@1` remain part of the canonical closeout surface.
- `V34-F` release-shape lock for v54 is frozen:
  - this arc is a standalone integrity self-verification and evidence slice only,
  - integrity scope must remain limited to the current standalone packaging manifest
    inventory, packaging provenance bindings, and emitted bundle files under explicit local
    artifact paths,
  - no installer/updater integration, archive fetch/unpack, or detached distribution flow is
    authorized in this arc,
  - no packaging, matrix, retry-context, attestation, or deployment semantics may be
    redefined in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `C1` Shared standalone integrity checker + deterministic verification-result baseline (`V34-F`)
2. `C2` Canonical standalone integrity evidence + guard suite (`V34-F`)

Out-of-scope note:

- installer or updater integration in this arc,
- archive fetch, unpack, or external bundle acquisition in this arc,
- detached checksum/signature distribution outside the current packaging-manifest authority
  surface in this arc,
- deployment-mode expansion (`V34-G`) in this arc,
- live remote verifier transport or attested execution expansion in this arc,
- broader policy recomputation beyond the current runner validator in this arc,
- packaging-equivalence recomputation outside verifier lane in this arc,
- verifier/package rejection-diagnostic aggregation in this arc,
- multi-runtime matrix expansion in this arc,
- adapter-kind expansion beyond current passthrough support in this arc,
- multi-signer/quorum policy in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v54)

- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.
- future `V34-F` follow-on expansion only after v54 closure:
  - installer/updater integration over the released integrity result,
  - archive acquisition or unpack flows beyond explicit local artifact ingestion,
  - detached end-user checksum or manifest distribution outside the current packaging-manifest
    authority surface,
  - broader portability flows for relocated standalone bundles beyond the current packaged
    output root if needed under explicit future lock text.
- future `V34-E` follow-on expansion only after v53 closure:
  - live provider adapters beyond the frozen singleton test-provider surface,
  - network transport and remote job dispatch,
  - attested verifier ingestion without exact local-equivalence fallback,
  - additive trust-anchor registry extension only if the existing V34-A registry contract
    proves insufficient under explicit future lock text.
- future `V34-D` follow-on expansion only after v52 closure:
  - verifier/package rejection-diagnostic aggregation beyond the current runner surface,
  - automatic retry prompt assembly or execution orchestration,
  - richer excerpt families beyond rejection diagnostics and canonical candidate-plan hunks.
- future `V34-B` follow-on expansion only after v50 closure:
  - multi-runtime lane expansion,
  - adapter-kind expansion beyond `candidate_plan_passthrough`,
  - matrix parity beyond current released adapter/mode sets.

## V53 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md",
  "target": "V34-F-baseline",
  "required_continuity_guards": [
    "V34_E_B1_ATTESTATION_BASELINE_GREEN",
    "V34_E_B2_ATTESTATION_GUARDS_GREEN"
  ],
  "expected_relation": "v53_attestation_baseline_and_closeout_contracts_remain_frozen_while_v34f_standalone_integrity_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v54.
- this narrowed machine-checkable consumption block is v53-local only and does not weaken the
  global continuity locks declared above; v36-v53 baseline continuity remains in force for
  the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-F Standalone Integrity Contract (Machine-Checkable)

```json
{
  "schema": "v34f_standalone_integrity_contract@1",
  "target_arc": "vNext+54",
  "target_path": "V34-F",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "verification_result_schema": "binding_and_continuity_sibling_artifact_only_not_primary_integrity_hash_subject",
    "packaging_result_schema": "binding_and_continuity_sibling_artifact_only_not_primary_integrity_hash_subject",
    "packaging_manifest_schema": "taskpack_ux_packaging_manifest@1",
    "packaging_provenance_schema": "taskpack_packaging_provenance@1",
    "v34a_handoff_completion_contract": "required_frozen_precondition",
    "v34b_matrix_baseline_contract": "required_frozen_precondition",
    "v34c_policy_recompute_contract": "required_frozen_precondition",
    "v34d_retry_context_contract": "required_frozen_precondition",
    "v34e_attestation_contract": "required_frozen_precondition"
  },
  "integrity_scope_requirements": {
    "standalone_integrity_verification_result_schema": "standalone_integrity_verification_result@1",
    "shared_integrity_checker_required": true,
    "input_mode": "explicit_local_artifact_ingestion_only_missing_required_paths_fail_closed",
    "deployment_mode_policy": "standalone_only_exact_case_sensitive_match",
    "integrity_authority_source_policy": "current_standalone_packaging_manifest_emitted_file_inventory_plus_actual_emitted_bundle_files_under_declared_bundle_root_only_no_network_fetch_no_installer_or_unpack_inference",
    "packaging_manifest_bundle_hash_subject_policy": "sha256_canonical_json_of_manifest_emitted_files_records_only",
    "verification_result_input_policy": "binding_and_continuity_sibling_artifact_only_not_integrity_hash_subject",
    "packaging_result_input_policy": "binding_and_continuity_sibling_artifact_only_not_integrity_hash_subject",
    "packaging_provenance_binding_required": true,
    "packaging_provenance_binding_policy": "bind_by_full_canonical_taskpack_packaging_provenance_artifact_hash",
    "current_packaging_materialization_required": true,
    "current_packaging_materialization_source_policy": "must_be_materialized_in_current_v54_flow_from_same_authoritative_inputs_not_reused_from_stale_external_bundle",
    "current_packaging_materialization_failure_outcome": "fail_closed_cannot_establish_integrity",
    "bundle_root_input_required": true,
    "bundle_root_resolution_policy": "single_explicit_local_standalone_bundle_root_input_must_be_consistent_with_manifest_emitted_paths_no_best_common_prefix_or_path_inference",
    "manifest_path_domain_policy": "manifest_emitted_paths_are_bundle_relative_to_declared_bundle_root_only",
    "manifest_emitted_file_row_fields": [
      "path",
      "sha256"
    ],
    "manifest_emitted_file_order_policy": "lexicographic_over_path",
    "manifest_normalized_emitted_path_duplicate_policy": "duplicate_normalized_manifest_emitted_paths_after_normalization_forbidden_fail_closed",
    "emitted_path_normalization_policy": "bundle_relative_posix_after_bundle_root_resolution",
    "normalized_emitted_path_duplicate_policy": "duplicate_normalized_emitted_paths_after_normalization_forbidden_fail_closed",
    "normalized_emitted_path_escape_policy": "normalized_paths_or_symlinks_escaping_declared_bundle_root_forbidden_fail_closed",
    "symlink_policy": "all_symlinks_forbidden",
    "emitted_file_inventory_exact_match_required": true,
    "missing_or_extra_bundle_files_fail_closed": true,
    "emitted_file_type_policy": "regular_files_only_non_regular_files_fail_closed",
    "file_hash_algorithm_policy": "sha256_bytes_hex_lowercase",
    "actual_emitted_file_hash_recompute_required": true,
    "integrity_checker_procedure_policy": "recompute_sha256_over_actual_emitted_file_bytes_build_canonical_bundle_relative_inventory_require_exact_row_set_and_order_equality_with_manifest_then_recompute_manifest_bundle_hash_subject_and_require_exact_equality",
    "result_emission_policy": "emit_deterministic_typed_result_artifact_on_all_success_and_fail_closed_paths_including_input_validation_failures_before_final_verdict",
    "raw_repo_reads_forbidden": true,
    "auto_fetch_or_unpack_forbidden": true,
    "replay_nondeterministic_fields_forbidden": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths_outside_bundle_root",
      "network_endpoint",
      "random_nonce"
    ]
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34f_standalone_integrity_evidence@1",
    "canonical_closeout_evidence_required": true,
    "verification_passed_policy": "true_means_integrity_checker_validation_inventory_bundle_hash_guards_and_closeout_validation_passed_not_installer_success_or_deployment_mode_release",
    "shared_integrity_checker_identifier_policy": "frozen_module_function_path_or_registry_key_no_free_text",
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "integrity_checker_entrypoint",
      "shared_integrity_checker_used",
      "shared_integrity_checker_identifier",
      "shared_integrity_checker_identifier_policy",
      "standalone_packaging_result_path",
      "standalone_packaging_manifest_path",
      "standalone_packaging_provenance_path",
      "standalone_packaging_provenance_hash",
      "standalone_packaging_bundle_hash",
      "recomputed_manifest_bundle_hash",
      "standalone_integrity_verification_result_path",
      "standalone_integrity_verification_result_hash",
      "deployment_mode",
      "deployment_mode_standalone_only",
      "verification_result_semantic_input_forbidden",
      "packaging_manifest_schema_validated",
      "packaging_manifest_bundle_hash_subject_verified",
      "packaging_provenance_binding_verified",
      "packaging_provenance_artifact_hash_verified",
      "current_packaging_materialization_recomputed",
      "current_packaging_materialization_failure_fails_closed",
      "bundle_root_input_explicit",
      "manifest_paths_bundle_relative",
      "manifest_normalized_path_duplicates_forbidden",
      "normalized_emitted_path_duplicates_forbidden",
      "bundle_root_escape_forbidden",
      "symlinks_forbidden",
      "regular_files_only",
      "actual_emitted_file_hashes_recomputed",
      "emitted_file_inventory_exact_match_verified",
      "missing_or_extra_bundle_files_fail_closed",
      "integrity_result_emitted_on_failure",
      "integrity_result_emitted_on_input_validation_failure",
      "raw_repo_reads_forbidden",
      "auto_fetch_or_unpack_forbidden",
      "verification_passed",
      "verification_passed_policy",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v53",
      "notes"
    ]
  },
  "test_requirements": {
    "standalone_integrity_result_deterministic_for_identical_inputs": true,
    "standalone_only_deployment_mode_enforced": true,
    "current_packaging_materialization_required": true,
    "standalone_integrity_result_emitted_on_failure": true,
    "input_validation_failure_result_emission_required": true,
    "manifest_normalized_path_duplicate_fail_closed": true,
    "normalized_emitted_path_duplicate_or_escape_fail_closed": true,
    "symlink_or_non_regular_file_fail_closed": true,
    "missing_or_extra_bundle_files_fail_closed": true,
    "packaging_manifest_bundle_hash_subject_verified": true,
    "actual_emitted_file_hash_recompute_required": true,
    "raw_repo_reads_forbidden": true,
    "auto_fetch_or_unpack_forbidden": true
  },
  "fail_closed_conditions": [
    "standalone_integrity_result_missing_after_validation",
    "standalone_integrity_result_not_emitted_on_failure",
    "input_validation_failure_without_result_artifact",
    "nonstandalone_deployment_mode_accepted",
    "packaging_manifest_schema_invalid_accepted",
    "packaging_manifest_bundle_hash_subject_drift_accepted",
    "verification_result_semantic_content_used_as_integrity_authority",
    "manifest_normalized_emitted_path_duplicate_accepted",
    "normalized_emitted_path_duplicate_accepted",
    "normalized_path_or_symlink_escape_from_bundle_root_accepted",
    "symlink_bundle_entry_accepted",
    "non_regular_bundle_file_accepted",
    "missing_or_extra_bundle_files_accepted",
    "actual_emitted_file_hash_recompute_skipped",
    "packaging_provenance_artifact_hash_drift_accepted",
    "current_packaging_output_not_materialized_in_v54_flow",
    "explicit_bundle_root_input_missing_or_inferred",
    "raw_repo_file_content_used_as_integrity_authority",
    "auto_fetch_or_unpack_released_in_v54",
    "standalone_integrity_evidence_missing_from_closeout"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## C1) Shared Standalone Integrity Checker + Deterministic Verification-Result Baseline (`V34-F`)

### Goal

Make `V34-F` real as a deterministic standalone bundle self-verification utility over the
current standalone packaging-manifest authority surface rather than ad hoc local checks.

### Scope

- extract or define a shared standalone integrity checker over the current standalone
  packaging-manifest inventory and emitted bundle files;
- emit deterministic `standalone_integrity_verification_result@1`;
- freeze integrity verification to manifest-authoritative emitted-file inventory plus
  packaging bundle hash;
- keep the first slice local-artifact only and standalone-only.

### Locks

- v54 must not widen integrity scope beyond the current standalone packaging-manifest
  authority surface.
- integrity input authority must derive only from:
  - canonical standalone packaging manifest,
  - canonical standalone packaging provenance and sibling packaging result bindings,
  - actual emitted standalone bundle files under the declared bundle root.
- `taskpack_verification_result@1` is preserved here as a binding and continuity sibling
  artifact only; it is not a semantic integrity authority input in this arc.
- `taskpack_packaging_result@1` is preserved here as a binding and continuity sibling
  artifact only; it is not the primary integrity hash subject.
- deployment mode must equal exact case-sensitive `standalone` in this arc.
- the packaging manifest bundle-hash subject remains the emitted-file row inventory only and
  must not silently widen to full-manifest hashing or alternate bundle subjects.
- manifest emitted-file `path` values are bundle-relative to the explicit declared
  standalone bundle root in this arc; they are not repo-relative paths.
- duplicate normalized manifest `path` entries after bundle-relative posix normalization are
  invalid and fail closed.
- duplicate normalized emitted paths after bundle-root-relative posix normalization are
  invalid and fail closed.
- all symlinks are forbidden in this arc; they are not accepted as manifest entries or
  bundle inventory entries.
- normalized emitted paths that escape the explicit declared bundle root are invalid and fail
  closed.
- bundle root must be supplied as an explicit local artifact input in the v54 flow and must
  be consistent with manifest-emitted paths; no best-common-prefix or similar inference is
  authorized.
- the checker must recompute file hashes from actual emitted bundle-file bytes, rebuild the
  canonical emitted-file inventory, require exact row equality with the manifest inventory,
  then recompute the manifest bundle-hash subject and require exact equality.
- manifest-emitted inventory may reference regular files only; non-regular filesystem
  objects fail closed.
- packaging provenance binding must be verified against the full canonical
  `taskpack_packaging_provenance@1` artifact hash.
- missing or extra emitted bundle files are invalid and fail closed.
- deterministic `standalone_integrity_verification_result@1` must be emitted on both intact
  and fail-closed paths, including input-validation failures, before the final integrity
  verdict is returned.
- raw repository reads outside the declared standalone bundle root are forbidden.
- installer/updater integration and archive fetch/unpack are forbidden in this arc.
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- identical inputs produce deterministic `standalone_integrity_verification_result@1` bytes
  across reruns;
- checker recomputes actual emitted-file hashes and reproduces the packaging-manifest bundle
  hash subject exactly for intact standalone outputs;
- missing or extra bundle files fail closed deterministically;
- failure paths still materialize deterministic
  `standalone_integrity_verification_result@1` before fail-closed verdict;
- manifest schema-invalid or bundle-root-invalid inputs still materialize deterministic
  `standalone_integrity_verification_result@1` before fail-closed verdict;
- non-standalone deployment mode inputs fail closed.

## C2) Canonical Standalone Integrity Evidence + Guard Suite (`V34-F`)

### Goal

Make the standalone integrity checker auditable and prove that it remains a local
manifest-authoritative verification lane without widening into installer or distribution
behavior.

### Scope

- add canonical closeout evidence for the v34f integrity lane;
- add deterministic guard coverage for:
  - checker determinism,
  - standalone-only deployment mode enforcement,
  - packaging-manifest bundle-hash subject verification,
  - missing or extra bundle-file rejection,
  - no raw repo reads or fetch/unpack behavior;
- integrate the integrity lane into canonical closeout evidence without changing packaging,
  attestation, or deployment semantics.

### Locks

- integrity evidence is closeout-authoritative only via deterministic artifact hash bindings.
- v54 must not make verifier, packaging, or stop-gate pass/fail decisions depend on
  installer/updater behavior because none is released in this arc.
- closeout proof must distinguish between:
  - `standalone_integrity_verification_result@1`,
  - standalone packaging manifest/result/provenance bindings,
  - docs-side `v34f_standalone_integrity_evidence@1`.
- standalone integrity posture must be encoded in both tests and closeout evidence.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v34f_standalone_integrity_evidence@1` block;
- guard suites prove standalone integrity verification remains deterministic and
  manifest-authoritative;
- no installer/updater or fetch/unpack authority path is released in this arc;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v54)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v54 closeout must include runtime-observability comparison row against v53 baseline.
- v54 closeout must include metric-key continuity assertion against v53 baseline.
- v54 closeout must include standalone integrity evidence block:
  - block schema is docs-only `v34f_standalone_integrity_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `integrity_checker_entrypoint`
    - `shared_integrity_checker_used`
    - `shared_integrity_checker_identifier`
    - `shared_integrity_checker_identifier_policy`
    - `standalone_packaging_result_path`
    - `standalone_packaging_manifest_path`
    - `standalone_packaging_provenance_path`
    - `standalone_packaging_provenance_hash`
    - `standalone_packaging_bundle_hash`
    - `recomputed_manifest_bundle_hash`
    - `standalone_integrity_verification_result_path`
    - `standalone_integrity_verification_result_hash`
    - `deployment_mode`
    - `deployment_mode_standalone_only`
    - `verification_result_semantic_input_forbidden`
    - `packaging_manifest_schema_validated`
    - `packaging_manifest_bundle_hash_subject_verified`
    - `packaging_provenance_binding_verified`
    - `packaging_provenance_artifact_hash_verified`
    - `current_packaging_materialization_recomputed`
    - `current_packaging_materialization_failure_fails_closed`
    - `bundle_root_input_explicit`
    - `manifest_paths_bundle_relative`
    - `manifest_normalized_path_duplicates_forbidden`
    - `normalized_emitted_path_duplicates_forbidden`
    - `bundle_root_escape_forbidden`
    - `symlinks_forbidden`
    - `regular_files_only`
    - `actual_emitted_file_hashes_recomputed`
    - `emitted_file_inventory_exact_match_verified`
    - `missing_or_extra_bundle_files_fail_closed`
    - `integrity_result_emitted_on_failure`
    - `integrity_result_emitted_on_input_validation_failure`
    - `raw_repo_reads_forbidden`
    - `auto_fetch_or_unpack_forbidden`
    - `verification_passed`
    - `verification_passed_policy`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v53`
    - `notes`

## Error/Exit Policy (v54)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v54 introduces new standalone integrity diagnostics, they must be constrained to an
  authoritative `AHK54xx` registry and remain error-only with non-zero exit behavior.
- If v54 introduces new integrity diagnostics, deterministic issue ordering must sort by
  `(issue_code, artifact_path, emitted_path)`.
- for standalone integrity exact-input subjects, `emitted_path` serializes in bundle-relative
  posix form under the explicit declared standalone bundle root.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34f standalone integrity checker baseline`
2. `tests: add v34f standalone integrity evidence and guard suite`

## Intermediate Preconditions (for v54 start)

1. v53 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v53 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS53.md`
3. Existing v53 attestation baseline remains available at v54 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/attestation.py`
   - `artifacts/agent_harness/v53/evidence_inputs/v34e_attestation_evidence_v53.json`
4. Existing packaging surfaces remain available at v54 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux_standalone.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
5. Existing v53 closeout artifacts remain available at v54 start:
   - `artifacts/quality_dashboard_v53_closeout.json`
   - `artifacts/stop_gate/metrics_v53_closeout.json`
   - `artifacts/stop_gate/report_v53_closeout.md`
   - `artifacts/agent_harness/v53/evidence_inputs/runtime_observability_comparison_v53.json`
   - `artifacts/agent_harness/v53/evidence_inputs/metric_key_continuity_assertion_v53.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No additional boundary release beyond the v53 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `C1` and `C2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-F` standalone integrity baseline remains local-artifact only and does not widen into
  installer/updater or deployment-mode behavior.
- v54 closeout evidence includes runtime-observability comparison row against v53 baseline,
  metric-key continuity assertion against v53 baseline, and
  `v34f_standalone_integrity_evidence@1`.
- `standalone_integrity_verification_result@1` is deterministic under identical inputs.
- `standalone_integrity_verification_result@1` is emitted on both intact and failure paths.
- packaging-manifest bundle-hash subject and emitted-file inventory exact match are verified.
- v36-v53 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
