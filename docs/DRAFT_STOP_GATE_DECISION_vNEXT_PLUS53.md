# Draft Stop-Gate Decision (Pre-Start vNext+53)

This note is the scaffold for the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md`

Status: pre-start threshold scaffold (March 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS53.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This scaffold becomes closeout-authoritative only after v53 implementation artifacts and final decision values are materialized."
}
```

## Decision Guardrail (Frozen)

- This scaffold records pre-start threshold expectations only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md`.
- This note does not authorize live remote verifier transport, remote job dispatch, or
  `remote_enclave` deployment-mode release by itself.
- Shared provider-neutral attestation validation, exact local-equivalence enforcement, and
  closeout evidence integration remain pending until implemented and proven on `main`.

## Planned Evidence Sources

- expected implementation PRs:
  - `B1` `contracts: add v34e attestation validation baseline`
  - `B2` `tests: add v34e equivalence and evidence guards`
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
  "baseline_arc": "vNext+52",
  "current_arc": "vNext+53",
  "baseline_source": "artifacts/stop_gate/report_v52_closeout.md",
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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v52_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v53_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v52": null
}
```

```json
{
  "schema": "v34e_attestation_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS53.md#v34e_attested_verifier_contract@1",
  "attestation_entrypoint": null,
  "shared_attestation_validator_used": null,
  "shared_attestation_validator_identifier": null,
  "shared_attestation_validator_identifier_policy": "frozen_module_function_path_or_registry_key_no_free_text",
  "local_verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "remote_enclave_attestation_path": null,
  "remote_enclave_attestation_hash": null,
  "attested_verified_result_path": null,
  "attested_verified_result_hash": null,
  "local_verified_result_path": null,
  "local_verified_result_hash": null,
  "attestation_verification_result_path": null,
  "attestation_verification_result_hash": null,
  "provider_id": null,
  "provider_id_closed_singleton_enforced": null,
  "provider_id_comparison_policy": "exact_case_sensitive_equality_against_deterministic_test_enclave",
  "attestation_trust_anchor_registry_reused": null,
  "runner_provenance_hash_policy": "sha256_over_full_taskpack_runner_provenance_at_1_canonical_json_artifact",
  "attestation_verified_required": true,
  "input_mode_artifact_ingestion_only": true,
  "attested_verified_result_schema_validated": null,
  "current_local_verification_recomputed": null,
  "current_local_verification_materialization_failure_fails_closed": true,
  "local_equivalence_required": true,
  "local_equivalence_subject_fields_verified": [
    "verified_result_hash"
  ],
  "local_equivalence_binding_fields_verified": null,
  "local_equivalence_verified": null,
  "opaque_provider_evidence_hash_audit_only": true,
  "normalized_claim_conflicts_forbidden": true,
  "remote_transport_or_job_dispatch_forbidden": true,
  "deployment_mode_expansion_forbidden": true,
  "verification_passed": null,
  "verification_passed_policy": "true_means_attestation_normalization_validation_local_equivalence_guards_and_closeout_validation_passed_not_policy_validation_packaging_validation_or_remote_job_success",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v52": null,
  "notes": "Populate at closeout with deterministic artifact hashes and exact local-equivalence proof."
}
```

## Exit-Criteria Scaffold (vNext+53)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `B1` merged with green CI | required | PR merge + CI run URL |
| `B2` merged with green CI | required | PR merge + CI run URL |
| Stop-gate schema-family continuity retained | required | `stop_gate_metrics@1` closeout metrics |
| Stop-gate metric-key continuity retained | required | v52/v53 exact-set equality assertion |
| Deterministic cardinality continuity retained (`80`) | required | closeout metrics key count |
| `remote_enclave_attestation@1` emitted and schema-valid | required | attestation artifact path/hash |
| `attestation_verification_result@1` emitted and schema-valid | required | validation artifact path/hash |
| Exact local-equivalence verified | required | attested/local verified result hash equality |
| Live transport / deployment-mode expansion remains absent | required | closeout evidence booleans |
| Canonical `v34e` evidence block emitted and hash-bound | required | v34e evidence input artifact |

## Pre-Start Recommendation

- gate decision:
  - `PENDING_IMPLEMENTATION`
- rationale:
  - v53 should proceed only as a thin provider-neutral attested verifier-ingestion baseline
    with exact local-equivalence and no live remote transport release.
