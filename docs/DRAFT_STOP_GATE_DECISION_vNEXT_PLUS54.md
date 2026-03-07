# Draft Stop-Gate Decision (Pre-Start vNext+54)

This note is the scaffold for the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`

Status: pre-start threshold scaffold (March 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This scaffold becomes closeout-authoritative only after v54 implementation artifacts and final decision values are materialized."
}
```

## Decision Guardrail (Frozen)

- This scaffold records pre-start threshold expectations only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`.
- This note does not authorize installer/updater behavior, archive fetch/unpack flows, or
  deployment-mode release by itself.
- Shared standalone integrity verification, deterministic integrity-result emission, and
  closeout evidence integration remain pending until implemented and proven on `main`.

## Planned Evidence Sources

- expected implementation PRs:
  - `C1` `contracts: add v34f standalone integrity checker baseline`
  - `C2` `tests: add v34f standalone integrity evidence and guard suite`
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
  "baseline_arc": "vNext+53",
  "current_arc": "vNext+54",
  "baseline_source": "artifacts/stop_gate/report_v53_closeout.md",
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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v53_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v54_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v53": null
}
```

```json
{
  "schema": "v34f_standalone_integrity_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md#v34f_standalone_integrity_contract@1",
  "integrity_checker_entrypoint": null,
  "shared_integrity_checker_used": null,
  "shared_integrity_checker_identifier": null,
  "shared_integrity_checker_identifier_policy": "frozen_module_function_path_or_registry_key_no_free_text",
  "standalone_packaging_result_path": null,
  "standalone_packaging_manifest_path": null,
  "standalone_packaging_provenance_path": null,
  "standalone_packaging_provenance_hash": null,
  "standalone_packaging_bundle_hash": null,
  "recomputed_manifest_bundle_hash": null,
  "standalone_integrity_verification_result_path": null,
  "standalone_integrity_verification_result_hash": null,
  "deployment_mode": "standalone",
  "deployment_mode_standalone_only": true,
  "verification_result_semantic_input_forbidden": true,
  "packaging_manifest_schema_validated": null,
  "packaging_manifest_bundle_hash_subject_verified": null,
  "packaging_provenance_binding_verified": null,
  "packaging_provenance_artifact_hash_verified": null,
  "current_packaging_materialization_recomputed": null,
  "current_packaging_materialization_failure_fails_closed": true,
  "bundle_root_input_explicit": null,
  "manifest_paths_bundle_relative": null,
  "manifest_normalized_path_duplicates_forbidden": true,
  "normalized_emitted_path_duplicates_forbidden": true,
  "bundle_root_escape_forbidden": true,
  "symlinks_forbidden": true,
  "regular_files_only": true,
  "actual_emitted_file_hashes_recomputed": null,
  "emitted_file_inventory_exact_match_verified": null,
  "missing_or_extra_bundle_files_fail_closed": true,
  "integrity_result_emitted_on_failure": null,
  "integrity_result_emitted_on_input_validation_failure": null,
  "raw_repo_reads_forbidden": true,
  "auto_fetch_or_unpack_forbidden": true,
  "verification_passed": null,
  "verification_passed_policy": "true_means_integrity_checker_validation_inventory_bundle_hash_guards_and_closeout_validation_passed_not_installer_success_or_deployment_mode_release",
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v53": null,
  "notes": "Populate at closeout with deterministic artifact hashes and standalone manifest-authoritative verification proof."
}
```

## Exit-Criteria Scaffold (vNext+54)

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `C1` merged with green CI | required | PR merge + CI run URL |
| `C2` merged with green CI | required | PR merge + CI run URL |
| Stop-gate schema-family continuity retained | required | `stop_gate_metrics@1` closeout metrics |
| Stop-gate metric-key continuity retained | required | v53/v54 exact-set equality assertion |
| Deterministic cardinality continuity retained (`80`) | required | closeout metrics key count |
| `standalone_integrity_verification_result@1` emitted and schema-valid | required | integrity result artifact path/hash |
| `standalone_integrity_verification_result@1` emitted on failure paths too | required | guard coverage + evidence booleans |
| Input-validation failures still emit typed integrity results | required | guard coverage + evidence booleans |
| Standalone-only deployment mode enforced | required | integrity result + evidence booleans |
| Packaging-manifest bundle-hash subject verified | required | integrity result + evidence booleans |
| Recomputed manifest bundle hash recorded | required | declared vs recomputed hash fields |
| Full packaging-provenance artifact hash binding verified | required | provenance path/hash + evidence booleans |
| Explicit bundle-root input and bundle-relative path domain verified | required | integrity result + evidence booleans |
| Manifest duplicate paths, symlinks, and non-regular files fail closed | required | guard coverage + evidence booleans |
| Missing or extra bundle files fail closed | required | guard coverage + evidence booleans |
| Canonical `v34f` evidence block emitted and hash-bound | required | v34f evidence input artifact |

## Pre-Start Recommendation

- gate decision:
  - `PENDING_IMPLEMENTATION`
- rationale:
  - v54 should proceed only as a thin standalone integrity self-verification baseline over
    current packaging-manifest authority, without widening into installer, updater, or
    distribution behavior.
