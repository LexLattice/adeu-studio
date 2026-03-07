# Draft Stop-Gate Decision (Pre-Start vNext+55)

This note is the scaffold for the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md`

Status: pre-start threshold scaffold (March 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This scaffold becomes closeout-authoritative only after v55 implementation artifacts and final decision values are materialized."
}
```

## Decision Guardrail (Frozen)

- This scaffold records pre-start threshold expectations only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md`.
- This note does not authorize live remote transport, remote job dispatch, provider
  expansion, or generalized remote execution release by itself.
- Shared remote-enclave deployment-mode packaging, deterministic three-mode matrix parity,
  and closeout evidence integration remain pending until implemented and proven on `main`.

## Planned Evidence Sources

- expected implementation PRs:
  - `D1` `contracts: add v34g remote_enclave deployment mode baseline`
  - `D2` `tests: add v34g remote_enclave parity evidence guards`
- expected local gate:
  - `make check`
- required closeout validation command:
  - `make closeout-lint`

## Planned Closeout Evidence Blocks (Scaffold)

```json
{
  "schema": "runtime_observability_comparison@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_arc": "vNext+54",
  "current_arc": "vNext+55",
  "baseline_source": "artifacts/stop_gate/report_v54_closeout.md",
  "current_source": null,
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "Populate at closeout; informational-only unless a future lock changes runtime observability policy."
}
```

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v54_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v55_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v54": null
}
```

```json
{
  "schema": "v34g_remote_enclave_mode_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md#v34g_remote_enclave_mode_contract@1",
  "remote_enclave_packager_entrypoint": null,
  "shared_remote_enclave_packager_used": null,
  "shared_remote_enclave_packager_identifier": null,
  "matrix_registry_path": null,
  "matrix_report_path": null,
  "matrix_report_hash": null,
  "remote_enclave_packaging_result_path": null,
  "remote_enclave_packaging_result_hash": null,
  "remote_enclave_packaging_manifest_path": null,
  "remote_enclave_packaging_manifest_hash": null,
  "remote_enclave_packaging_provenance_path": null,
  "remote_enclave_packaging_provenance_hash": null,
  "remote_enclave_attestation_path": null,
  "remote_enclave_attestation_hash": null,
  "attestation_verification_result_path": null,
  "attestation_verification_result_hash": null,
  "deployment_mode_enum": [
    "adeu_integrated",
    "remote_enclave",
    "standalone"
  ],
  "deployment_modes_covered": null,
  "deployment_modes_covered_policy": "lexicographically_sorted_exact_list_equal_to_deployment_mode_enum",
  "remote_enclave_mode_present": null,
  "provider_id_singleton": "deterministic_test_enclave",
  "provider_id_singleton_enforced": null,
  "provider_id_comparison_policy": "exact_case_sensitive_no_aliases_or_normalization",
  "attestation_contract_reused": null,
  "attestation_artifact_ingestion_only": null,
  "attestation_verified_required": true,
  "attestation_binding_fields": [
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verified_result_hash",
    "provider_id",
    "attestation_verified"
  ],
  "attestation_binding_fields_verified": null,
  "attestation_binding_fields_verified_policy": "refers_only_to_current_v55_attestation_prerequisite_set",
  "remote_transport_or_job_dispatch_forbidden": true,
  "deployment_mode_exact_case_sensitive": true,
  "deployment_mode_source_required": true,
  "deployment_mode_dual_source_conflict_rejected": true,
  "runtime_id_comparison_policy": "exact_case_sensitive_singleton_no_aliases_or_normalization",
  "lexicographic_lane_order_enforced": null,
  "lane_count_formula": "3_times_declared_adapter_count_under_singleton_runtime",
  "declared_adapter_count_source_policy": "derived_only_from_adapter_matrix_at_1_not_from_report_rows_or_runtime_discovery",
  "canonical_subtree_exact_match_required": true,
  "allowed_noncanonical_mode_difference_scope": "bundle_wrapper_and_taskpack_ux_mode_bundle_surface_only",
  "attestation_metadata_canonical_leakage_forbidden": true,
  "policy_equivalence_exact_match_required": true,
  "lane_count": null,
  "report_covers_all_declared_lanes": null,
  "verification_passed": null,
  "verification_passed_policy": "true_means_v55_deployment_mode_extension_guard_suite_and_closeout_validation_passed_not_live_remote_execution_provider_expansion_or_attestation_semantics_beyond_frozen_prerequisite_checks",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v54": null,
  "notes": "Populate at closeout with deterministic remote_enclave packaging, three-mode matrix parity, and non-transport proof."
}
```

## Exit-Criteria Scaffold (vNext+55)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `D1` merged with green CI | required | PR merge + CI run URL |
| `D2` merged with green CI | required | PR merge + CI run URL |
| Stop-gate schema-family continuity retained | required | `stop_gate_metrics@1` closeout metrics |
| Stop-gate metric-key continuity retained | required | v54/v55 exact-set equality assertion |
| Deterministic cardinality continuity retained (`80`) | required | closeout metrics key count |
| Remote-enclave packaging artifacts emitted and schema-valid | required | packaging result/manifest/provenance paths |
| Deployment-mode enum covers exactly integrated / remote_enclave / standalone | required | matrix registry + v34g evidence |
| Explicit deployment-mode source required | required | v34g evidence + guard coverage |
| Remote-enclave mode fails closed without valid attestation prerequisites | required | v34g evidence + guard coverage |
| Three-mode matrix report emitted and schema-valid | required | matrix registry/report artifacts |
| Remote-enclave lane present exactly once per declared adapter/runtime | required | matrix report + v34g evidence |
| Lane count equals `3 × declared_adapter_count` | required | matrix report + v34g evidence |
| Canonical subtree parity retained across all three modes | required | matrix report + v34g evidence |
| Policy-equivalence parity retained across all three modes | required | matrix report + v34g evidence |
| Live remote transport and job dispatch remain absent | required | v34g evidence booleans |
| Singleton provider posture retained | required | v34g evidence |
| Canonical `v34g` evidence block emitted and hash-bound | required | v34g evidence input artifact |

## Pre-Start Recommendation

- gate decision:
  - `PENDING_IMPLEMENTATION`
- rationale:
  - v55 should proceed only as a thin `remote_enclave` deployment-mode extension over the
    current packaging/matrix/attestation contracts, without widening into live remote
    execution behavior.
