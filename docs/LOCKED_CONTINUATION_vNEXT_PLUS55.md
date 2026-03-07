# Locked Continuation vNext+55 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md`
- `docs/ASSESSMENT_vNEXT_PLUS54_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 7, 2026 UTC).

## Decision Basis

- `vNext+54` (`V34-F`, `C1`/`C2`) is merged on `main` with green CI checks.
- `vNext+54` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS54_EDGES.md` marks the standalone `V34-F` integrity baseline
  as closed and restores eligibility for explicit `V34-G` evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-G` as the next deferred family candidate
  after `V34-F`.
- current harness reality is narrower than a full live `remote_enclave` execution lane:
  - packaging deployment mode is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`,
  - deployment mode remains frozen to `adeu_integrated` / `standalone` on `main`,
  - declared matrix parity is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`,
  - provider-neutral attestation validation is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/attestation.py`,
  - no released `remote_enclave` packaging result, manifest, or provenance lane exists on
    `main`,
  - no released matrix/report contract covers a `remote_enclave` deployment-mode row on
    `main`,
  - no released `v34g_remote_enclave_mode_evidence@1` block exists on `main`,
  - no live remote transport, remote job dispatch, or provider expansion is authorized on
    `main`.
- `vNext+55` therefore selects one thin `V34-G` baseline slice only:
  - explicit deployment-mode enum expansion to `remote_enclave` over the current adapter
    and singleton runtime surfaces,
  - deterministic `remote_enclave` packaging artifacts over frozen local artifact-ingestion
    and attestation-prerequisite posture,
  - deterministic three-mode matrix/report/evidence update over the frozen parity subject,
  - canonical closeout evidence integration plus guard coverage,
  - no live remote transport, job dispatch, or provider expansion in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v55,
  - v55 keyset must be exactly equal to v54 keyset,
  - baseline derived cardinality at v55 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v55 is explicit and narrow:
  - this arc authorizes one `L1` deployment-mode extension lane only,
  - no governance or persistence authority release is authorized in this arc,
  - no live remote execution transport, remote job dispatch, or generalized `L2`
    boundary release is authorized in this arc.
- `V34-A` signing and downstream-handoff completion remain frozen prerequisites.
- `V34-B` matrix baseline remains a frozen prerequisite:
  - declared registry/report contracts remain authoritative,
  - current released lane tuple `(deployment_mode, adapter_id, runtime_id)` remains
    authoritative,
  - runtime remains frozen to singleton `local_python_cli` in this arc,
  - adapter-kind expansion beyond `candidate_plan_passthrough` is not authorized in this
    arc.
- `V34-C` verifier-lane policy-recompute baseline remains a frozen prerequisite.
- `V34-D` retry-context baseline remains a frozen prerequisite.
- `V34-E` attestation baseline remains a frozen prerequisite:
  - provider-neutral attestation normalization remains authoritative,
  - exact local-equivalence and trust-anchor reuse remain unchanged,
  - singleton provider posture remains frozen to `deterministic_test_enclave` in this arc.
- `V34-F` standalone integrity baseline remains a frozen prerequisite:
  - manifest-authoritative integrity verification remains unchanged,
  - standalone integrity release does not widen deployment-mode behavior by itself.
- `V34-G` release-shape lock for v55 is frozen:
  - this arc is a deployment-mode extension and evidence slice only,
  - `remote_enclave` mode must remain local-artifact-ingestion-only and attestation-bound,
  - no live provider adapter, network transport, or remote job dispatch is authorized in
    this arc,
  - no packaging, matrix, attestation, retry-context, or policy semantics may be redefined
    beyond the explicit deployment-mode extension in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `D1` Remote-enclave deployment-mode enum expansion + deterministic packaging baseline (`V34-G`)
2. `D2` Remote-enclave mode parity evidence + guard suite (`V34-G`)

Out-of-scope note:

- live remote transport, remote job dispatch, or remote verifier execution in this arc,
- provider expansion beyond `deterministic_test_enclave` in this arc,
- attestation trust-anchor system fork or parallel registry in this arc,
- standalone integrity, installer/updater, archive fetch/unpack, or detached distribution
  changes in this arc,
- broader policy recomputation beyond the current runner validator in this arc,
- packaging-equivalence recomputation outside the frozen matrix subject in this arc,
- verifier/package rejection-diagnostic aggregation in this arc,
- multi-runtime matrix expansion in this arc,
- adapter-kind expansion beyond current passthrough support in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v55)

- future `V34-G` follow-on expansion only after v55 closure:
  - live remote transport or remote job dispatch,
  - provider expansion beyond the frozen singleton attestation provider,
  - remote-enclave execution without local artifact ingestion,
  - broader mode-specific bundle behavior beyond the frozen wrapper surface.
- future post-`V34-G` operational hardening only after v55 closure:
  - closeout orchestration extraction and artifact indexing from
    `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`.
- future `V34-F` follow-on expansion only after v54 closure:
  - installer/updater integration,
  - archive acquisition or unpack flows,
  - detached end-user checksum or manifest distribution.
- future `V34-B` follow-on expansion only after v50 closure:
  - multi-runtime lane expansion,
  - adapter-kind expansion beyond `candidate_plan_passthrough`.

## V54 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md",
  "target": "V34-G-baseline",
  "required_continuity_guards": [
    "V34_F_C1_STANDALONE_INTEGRITY_BASELINE_GREEN",
    "V34_F_C2_STANDALONE_INTEGRITY_GUARDS_GREEN"
  ],
  "expected_relation": "v54_standalone_integrity_baseline_and_closeout_contracts_remain_frozen_while_v34g_remote_enclave_mode_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v55.
- this narrowed machine-checkable consumption block is v54-local only and does not weaken
  the global continuity locks declared above; v36-v54 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-G Remote-Enclave Mode Contract (Machine-Checkable)

```json
{
  "schema": "v34g_remote_enclave_mode_contract@1",
  "target_arc": "vNext+55",
  "target_path": "V34-G",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "candidate_change_plan_hash": "required",
    "runner_provenance_schema": "taskpack_runner_provenance@1",
    "verification_result_schema": "binding_and_continuity_sibling_artifact_only_not_primary_deployment_mode_authority",
    "packaging_result_schema": "taskpack_packaging_result@1",
    "packaging_manifest_schema": "taskpack_ux_packaging_manifest@1",
    "packaging_provenance_schema": "taskpack_packaging_provenance@1",
    "matrix_registry_schema": "adapter_matrix@1",
    "matrix_report_schema": "adapter_matrix_parity_report@1",
    "remote_enclave_attestation_schema": "binding_and_continuity_prerequisite_only_not_live_execution_authority_input",
    "attestation_verification_result_schema": "binding_and_continuity_prerequisite_only_not_live_execution_authority_input",
    "v34a_handoff_completion_contract": "required_frozen_precondition",
    "v34b_matrix_baseline_contract": "required_frozen_precondition",
    "v34c_policy_recompute_contract": "required_frozen_precondition",
    "v34d_retry_context_contract": "required_frozen_precondition",
    "v34e_attestation_contract": "required_frozen_precondition",
    "v34f_standalone_integrity_contract": "required_frozen_precondition"
  },
  "mode_scope_requirements": {
    "shared_remote_enclave_packager_required": true,
    "shared_remote_enclave_packager_identifier_policy": "frozen_module_function_path_or_registry_key_no_free_text",
    "deployment_mode_enum": [
      "adeu_integrated",
      "remote_enclave",
      "standalone"
    ],
    "deployment_mode_exact_policy": "explicit_case_sensitive_input_only",
    "deployment_mode_source_policy": "explicit_cli_or_contract_input_only_no_host_environment_network_or_job_state_inference",
    "deployment_mode_source_required_policy": "absence_of_explicit_deployment_mode_input_fail_closed_no_default_or_inherited_state",
    "deployment_mode_dual_source_conflict_policy": "if_multiple_explicit_sources_are_present_they_must_match_exactly_else_fail_closed",
    "remote_enclave_packaging_materialization_required": true,
    "remote_enclave_packaging_materialization_failure_outcome": "fail_closed_cannot_establish_remote_enclave_mode",
    "remote_enclave_provider_id": "deterministic_test_enclave",
    "remote_enclave_provider_policy": "closed_singleton_reused_from_v34e_attestation_contract",
    "provider_id_comparison_policy": "exact_case_sensitive_no_aliases_or_normalization",
    "attestation_contract_reuse_required": true,
    "attestation_input_policy": "artifact_ingestion_only_no_live_remote_fetch_transport_or_job_dispatch",
    "attestation_precondition_policy": "if_deployment_mode_equals_remote_enclave_attestation_artifacts_must_be_present_schema_valid_hash_bound_to_current_authoritative_inputs_and_attestation_verified_true_else_fail_closed",
    "attestation_verified_must_equal_true": true,
    "remote_transport_or_job_dispatch_forbidden": true,
    "remote_execution_release_forbidden": true,
    "runtime_id_policy": "singleton_only_local_python_cli",
    "runtime_id_comparison_policy": "exact_case_sensitive_singleton_no_aliases_or_normalization",
    "adapter_kind_policy": "candidate_plan_passthrough_only_non_v55_expansion_forbidden",
    "matrix_lane_tuple": [
      "deployment_mode",
      "adapter_id",
      "runtime_id"
    ],
    "matrix_lane_order_policy": "lexicographic_over_deployment_mode_adapter_id_runtime_id",
    "lane_pairing_policy": "for_each_declared_adapter_id_exactly_three_deployment_mode_rows_required_under_singleton_runtime_id",
    "lane_count_formula": "3_times_declared_adapter_count_under_singleton_runtime",
    "declared_adapter_count_source_policy": "derived_only_from_adapter_matrix_at_1_not_from_report_rows_or_runtime_discovery",
    "deployment_modes_covered_policy": "lexicographically_sorted_exact_list_equal_to_deployment_mode_enum",
    "canonical_subtree_exact_match_required": true,
    "canonical_subtree_source_policy": "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only",
    "allowed_noncanonical_mode_difference_scope": "bundle_wrapper_and_taskpack_ux_mode_bundle_surface_only",
    "attestation_metadata_surface_policy": "remote_enclave_specific_attestation_metadata_only_in_frozen_noncanonical_wrapper_surface_never_in_canonical_subtree_or_policy_equivalence_subject",
    "attestation_binding_fields": [
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verified_result_hash",
      "provider_id",
      "attestation_verified"
    ],
    "attestation_binding_fields_verified_policy": "refers_only_to_current_v55_attestation_prerequisite_set",
    "policy_equivalence_exact_match_required": true,
    "policy_equivalence_required_keys": [
      "issue_code_set",
      "required_evidence_slots_filled",
      "allowlist_violations",
      "forbidden_effects_detected"
    ],
    "mode_specific_policy_override": "forbidden_fail_closed",
    "matrix_report_completeness_policy": "every_declared_lane_must_appear_exactly_once",
    "remote_enclave_mode_presence_required": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34g_remote_enclave_mode_evidence@1",
    "canonical_closeout_evidence_required": true,
    "verification_passed_policy": "true_means_v55_deployment_mode_extension_guard_suite_and_closeout_validation_passed_not_live_remote_execution_provider_expansion_or_attestation_semantics_beyond_frozen_prerequisite_checks",
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "remote_enclave_packager_entrypoint",
      "shared_remote_enclave_packager_used",
      "shared_remote_enclave_packager_identifier",
      "matrix_registry_path",
      "matrix_report_path",
      "matrix_report_hash",
      "remote_enclave_packaging_result_path",
      "remote_enclave_packaging_result_hash",
      "remote_enclave_packaging_manifest_path",
      "remote_enclave_packaging_manifest_hash",
      "remote_enclave_packaging_provenance_path",
      "remote_enclave_packaging_provenance_hash",
      "remote_enclave_attestation_path",
      "remote_enclave_attestation_hash",
      "attestation_verification_result_path",
      "attestation_verification_result_hash",
      "deployment_mode_enum",
      "deployment_modes_covered",
      "deployment_modes_covered_policy",
      "remote_enclave_mode_present",
      "provider_id_singleton",
      "provider_id_singleton_enforced",
      "provider_id_comparison_policy",
      "attestation_contract_reused",
      "attestation_artifact_ingestion_only",
      "attestation_verified_required",
      "attestation_binding_fields",
      "attestation_binding_fields_verified",
      "attestation_binding_fields_verified_policy",
      "remote_transport_or_job_dispatch_forbidden",
      "deployment_mode_exact_case_sensitive",
      "deployment_mode_source_required",
      "deployment_mode_dual_source_conflict_rejected",
      "runtime_id_comparison_policy",
      "lexicographic_lane_order_enforced",
      "lane_count_formula",
      "declared_adapter_count_source_policy",
      "canonical_subtree_exact_match_required",
      "allowed_noncanonical_mode_difference_scope",
      "attestation_metadata_canonical_leakage_forbidden",
      "policy_equivalence_exact_match_required",
      "lane_count",
      "report_covers_all_declared_lanes",
      "verification_passed",
      "verification_passed_policy",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v54",
      "notes"
    ]
  },
  "test_requirements": {
    "remote_enclave_packaging_result_emitted": true,
    "remote_enclave_mode_fails_without_valid_attestation": true,
    "remote_enclave_mode_fails_without_explicit_deployment_mode_source": true,
    "matrix_report_includes_remote_enclave_lane": true,
    "undeclared_or_out_of_order_remote_enclave_lane_rejected": true,
    "deployment_mode_dual_source_conflict_rejected": true,
    "provider_id_outside_singleton_rejected": true,
    "remote_transport_or_job_dispatch_forbidden": true,
    "remote_enclave_canonical_subtree_parity_exact": true
  },
  "fail_closed_conditions": [
    "remote_enclave_deployment_mode_accepted_without_explicit_enum_expansion",
    "remote_enclave_lane_missing_from_declared_matrix_or_report",
    "remote_enclave_mode_established_without_valid_attestation_prerequisites",
    "remote_enclave_mode_established_without_explicit_deployment_mode_source",
    "remote_enclave_canonical_subtree_parity_mismatch_accepted",
    "remote_enclave_policy_equivalence_mismatch_accepted",
    "remote_transport_or_job_dispatch_released_in_v55",
    "deployment_mode_dual_source_conflict_accepted",
    "provider_id_outside_deterministic_test_enclave_accepted",
    "attestation_contract_bypassed_for_remote_enclave_mode",
    "attestation_metadata_leaked_into_canonical_subtree_or_policy_equivalence_subject",
    "mode_specific_policy_override_accepted",
    "noncanonical_divergence_beyond_frozen_wrapper_scope_accepted",
    "v34g_remote_enclave_mode_evidence_missing_from_closeout"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## D1) Remote-Enclave Deployment-Mode Enum Expansion + Deterministic Packaging Baseline (`V34-G`)

### Goal

Make `V34-G` real as a narrow deployment-mode extension over the current packaging and
matrix contracts without releasing live remote execution behavior.

### Scope

- expand the deployment-mode enum to include `remote_enclave`;
- add deterministic `remote_enclave` packaging result, manifest, and provenance artifacts;
- keep `remote_enclave` mode bound to the frozen local-artifact-ingestion and attestation
  prerequisite posture.

### Locks

- `remote_enclave` must not widen provider scope beyond `deterministic_test_enclave`.
- `deployment_mode` must be supplied from an explicit allowed source; absence of an explicit
  deployment-mode input fails closed and must not fall back to defaults or inherited state.
- if `deployment_mode == "remote_enclave"`, attestation prerequisites must be present,
  schema-valid, hash-bound to the current authoritative inputs, and
  `attestation_verified == true`; otherwise mode materialization fails closed.
- `remote_enclave` must not release live transport, job dispatch, or remote execution in
  this arc.
- canonical subtree parity must remain exact against the existing released subject family.
- any mode-specific divergence must stay inside the frozen noncanonical bundle wrapper /
  mode bundle surface only.
- any `remote_enclave`-specific attestation metadata must remain inside that frozen
  noncanonical surface only and must never enter the canonical subtree or the
  policy-equivalence subject.
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

### Acceptance

- identical inputs produce deterministic `remote_enclave` packaging artifacts across reruns;
- `remote_enclave` packaging artifacts remain schema-valid and case-sensitive on
  `deployment_mode`;
- `remote_enclave` canonical subtree matches the existing released parity subject exactly.

## D2) Remote-Enclave Mode Parity Evidence + Guard Suite (`V34-G`)

### Goal

Make the `remote_enclave` deployment-mode extension auditable and prove that it preserves the
frozen parity/equivalence guarantees rather than redefining them.

### Scope

- extend the declared matrix/report/evidence surfaces to cover the third deployment mode;
- add canonical `v34g_remote_enclave_mode_evidence@1`;
- add guard coverage for enum exactness, lane completeness, parity exactness, and forbidden
  live transport/provider expansion.

### Locks

- matrix lane ordering remains lexicographic over
  `(deployment_mode, adapter_id, runtime_id)`.
- per-adapter lane completeness must expand to exactly three deployment modes in this arc.
- lane count is exactly `3 × declared_adapter_count` in this arc because disabled rows,
  hidden lanes, and runtime expansion are all out of scope.
- `declared_adapter_count` must derive only from `adapter_matrix@1`; report rows and runtime
  discovery must not become authority sources for lane cardinality.
- `deployment_modes_covered` must serialize as the lexicographically sorted exact list
  `["adeu_integrated", "remote_enclave", "standalone"]`.
- `remote_enclave` mode remains deployment-surface only; the attestation lane remains
  authoritative for actual attested verifier validation.
- closeout proof must distinguish between:
  - remote_enclave packaging artifacts,
  - matrix/report parity proof,
  - docs-side `v34g_remote_enclave_mode_evidence@1`.

### Acceptance

- matrix/report artifacts include `remote_enclave` exactly once per declared adapter under
  the singleton runtime;
- canonical `v34g_remote_enclave_mode_evidence@1` is emitted and hash-bound in closeout;
- no provider, transport, or policy-scope widening is introduced by the mode extension.

## Stop-Gate Impact (v55)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v55 closeout must include runtime-observability comparison row against v54 baseline.
- v55 closeout must include metric-key continuity assertion against v54 baseline.
- v55 closeout must include remote-enclave mode evidence block:
  - block schema is docs-only `v34g_remote_enclave_mode_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `remote_enclave_packager_entrypoint`
    - `shared_remote_enclave_packager_used`
    - `shared_remote_enclave_packager_identifier`
    - `matrix_registry_path`
    - `matrix_report_path`
    - `matrix_report_hash`
    - `remote_enclave_packaging_result_path`
    - `remote_enclave_packaging_result_hash`
    - `remote_enclave_packaging_manifest_path`
    - `remote_enclave_packaging_manifest_hash`
    - `remote_enclave_packaging_provenance_path`
    - `remote_enclave_packaging_provenance_hash`
    - `remote_enclave_attestation_path`
    - `remote_enclave_attestation_hash`
    - `attestation_verification_result_path`
    - `attestation_verification_result_hash`
    - `deployment_mode_enum`
    - `deployment_modes_covered`
    - `deployment_modes_covered_policy`
    - `remote_enclave_mode_present`
    - `provider_id_singleton`
    - `provider_id_singleton_enforced`
    - `provider_id_comparison_policy`
    - `attestation_contract_reused`
    - `attestation_artifact_ingestion_only`
    - `attestation_verified_required`
    - `attestation_binding_fields`
    - `attestation_binding_fields_verified`
    - `attestation_binding_fields_verified_policy`
    - `remote_transport_or_job_dispatch_forbidden`
    - `deployment_mode_exact_case_sensitive`
    - `deployment_mode_source_required`
    - `deployment_mode_dual_source_conflict_rejected`
    - `runtime_id_comparison_policy`
    - `lexicographic_lane_order_enforced`
    - `lane_count_formula`
    - `declared_adapter_count_source_policy`
    - `canonical_subtree_exact_match_required`
    - `allowed_noncanonical_mode_difference_scope`
    - `attestation_metadata_canonical_leakage_forbidden`
    - `policy_equivalence_exact_match_required`
    - `lane_count`
    - `report_covers_all_declared_lanes`
    - `verification_passed`
    - `verification_passed_policy`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v54`
    - `notes`

## Error/Exit Policy (v55)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v55 introduces new deployment-mode-extension diagnostics, they must be constrained to
  an authoritative `AHK55xx` registry and remain error-only with non-zero exit behavior.
- If v55 introduces new mode-extension diagnostics, deterministic issue ordering must sort
  by `(issue_code, deployment_mode, adapter_id, runtime_id, artifact_path)`.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34g remote_enclave deployment mode baseline`
2. `tests: add v34g remote_enclave parity evidence guards`

## Intermediate Preconditions (for v55 start)

1. v54 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v54 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md`
3. Existing v54 standalone integrity baseline remains available at v55 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/standalone_integrity.py`
   - `artifacts/agent_harness/v54/evidence_inputs/v34f_standalone_integrity_evidence_v54.json`
4. Existing packaging/matrix/attestation surfaces remain available at v55 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/attestation.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
5. Existing v54 closeout artifacts remain available at v55 start:
   - `artifacts/quality_dashboard_v54_closeout.json`
   - `artifacts/stop_gate/metrics_v54_closeout.json`
   - `artifacts/stop_gate/report_v54_closeout.md`
   - `artifacts/agent_harness/v54/evidence_inputs/runtime_observability_comparison_v54.json`
   - `artifacts/agent_harness/v54/evidence_inputs/metric_key_continuity_assertion_v54.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No live remote execution, transport, or provider expansion beyond the v54 baseline is
   introduced before this arc is explicitly locked and implemented.

## Exit Criteria (Draft)

- `D1` and `D2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-G` remote-enclave mode baseline remains artifact-ingestion-only and does not widen
  into live transport, job dispatch, or provider expansion.
- v55 closeout evidence includes runtime-observability comparison row against v54 baseline,
  metric-key continuity assertion against v54 baseline, and
  `v34g_remote_enclave_mode_evidence@1`.
- `remote_enclave` packaging artifacts are deterministic under identical inputs.
- matrix/report parity covers all declared three-mode lanes and retains exact canonical
  subtree + policy-equivalence parity.
- v36-v54 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
