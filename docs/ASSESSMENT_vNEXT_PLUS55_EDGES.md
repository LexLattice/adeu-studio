# Assessment vNext+55 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+55` (`V34-G` optional
`remote_enclave` deployment-mode baseline).

Status: pre-lock assessment (March 7, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS55_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": true,
  "authoritative_scope": "v55_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This document is authoritative for v55 pre-lock edge planning until superseded by post-closeout disposition."
}
```

## Scope

- In scope: thin `V34-G` baseline over `remote_enclave` deployment-mode extension,
  deterministic remote-enclave packaging artifacts, three-mode matrix parity, and canonical
  closeout evidence integration.
- Out of scope: live remote transport, remote job dispatch, provider expansion, broader
  attested execution release, installer/updater/archive changes, stop-gate schema-family
  fork, metric-key expansion, and generalized `L2` release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS54.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS54.md`
- `docs/ASSESSMENT_vNEXT_PLUS54_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/attestation.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/tests/test_taskpack_packaging.py`
- `packages/adeu_agent_harness/tests/test_taskpack_verifier.py`
- `artifacts/quality_dashboard_v54_closeout.json`
- `artifacts/stop_gate/metrics_v54_closeout.json`
- `artifacts/agent_harness/v54/evidence_inputs/runtime_observability_comparison_v54.json`
- `artifacts/agent_harness/v54/evidence_inputs/metric_key_continuity_assertion_v54.json`
- `artifacts/agent_harness/v54/evidence_inputs/v34e_attestation_evidence_v54.json`
- `artifacts/agent_harness/v54/evidence_inputs/v34f_standalone_integrity_evidence_v54.json`
- `artifacts/agent_harness/v50/matrix/adapter_matrix.json`
- `artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json`

## Current Repo Reality

1. Packaging deployment mode is real and deterministic on `main`.
   - `package_ux.py` freezes deployment mode to `adeu_integrated` / `standalone`.
2. Declared matrix parity is real and deterministic on `main`.
   - `matrix_parity.py` freezes the current deployment-mode enum to exactly those two modes
     under singleton runtime `local_python_cli`.
3. Provider-neutral attestation validation is real and deterministic on `main`.
   - `attestation.py` already freezes local-artifact-ingestion-only attestation validation
     and singleton provider `deterministic_test_enclave`.
4. No released `remote_enclave` deployment-mode packaging lane exists on `main`.
5. No released three-mode matrix registry/report or canonical `v34g` closeout evidence
   exists on `main`.

## Pre-Lock Edge Set (Draft)

1. Deployment-mode enum expansion gap: `open`.
   - `package_ux.py` and `matrix_parity.py` currently freeze the enum to two modes only.
2. Remote-enclave packaging lane absence risk: `open`.
   - no released packaging result/manifest/provenance surface exists for
     `deployment_mode == "remote_enclave"`.
3. Three-mode matrix completeness gap: `open`.
   - current matrix contracts assume exactly two deployment-mode rows per declared adapter.
4. Live remote transport overreach risk: `open`.
   - `V34-G` can accidentally widen into transport or job-dispatch behavior unless frozen
     out explicitly.
5. Provider expansion creep risk: `open`.
   - `remote_enclave` naming can drift into multi-provider behavior unless the singleton
     `deterministic_test_enclave` posture remains explicit.
6. Attestation-bypass risk: `open`.
   - a `remote_enclave` mode could implicitly bypass the closed `V34-E` attestation contract
     instead of reusing it.
7. Deployment-mode source ambiguity risk: `open`.
   - mode selection must remain explicit and case-sensitive rather than inferred from host,
     network, or job state.
8. Mode-specific policy-override risk: `open`.
   - the new deployment mode must not redefine allowlist/forbidden or evidence-slot policy.
9. Canonical subtree parity drift risk: `open`.
   - remote-enclave mode must preserve exact canonical parity with the existing released
     subject family.
10. Wrapper-surface exception ambiguity risk: `open`.
   - any mode-specific divergence must stay inside a narrowly frozen noncanonical wrapper
     surface.
11. Attestation artifact-ingestion-only ambiguity risk: `open`.
   - the mode must remain tied to local attestation artifact ingestion rather than live
     fetch or execution.
12. Packaging schema drift risk: `open`.
   - adding a third deployment mode must not silently fork packaging result/manifest/
     provenance schema families.
13. Matrix report/evidence integration gap: `open`.
   - no canonical `v34g_remote_enclave_mode_evidence@1` closeout slot exists on `main`.
14. Stop-gate churn risk: `open`.
   - v55 should not widen stop-gate schema family or metric cardinality.
15. Runtime/adaptor expansion creep risk: `open`.
   - remote-enclave mode should not silently widen runtime_id or adapter-kind surfaces.
16. Provider-id exactness ambiguity risk: `open`.
   - singleton provider comparison should remain exact and case-sensitive.
17. Deployment-mode ordering drift risk: `open`.
   - three-mode registry/report ordering needs a deterministic lexicographic rule.
18. Existing integrated/standalone regression risk: `open`.
   - adding a third mode must not weaken or perturb the already closed two-mode parity
     baseline.
19. Remote-enclave evidence proof gap: `open`.
   - closeout must prove the mode is present, parity-preserving, attestation-bound, and
     non-transport.
20. Boundary-release overclaim risk: `open`.
   - `V34-G` must not be mistaken for generalized remote execution release.
21. Attestation-precondition ambiguity risk: `open`.
   - `remote_enclave` mode must fail closed unless the reused attestation prerequisites are
     present, schema-valid, hash-bound, and `attestation_verified == true`.
22. Deployment-mode dual-source conflict risk: `open`.
   - explicit CLI and contract deployment-mode inputs must not silently disagree.
23. Lane-count formula ambiguity risk: `open`.
   - the three-mode extension should pin `lane_count = 3 × declared_adapter_count` under
     the frozen singleton runtime.
24. Canonical attestation-metadata leakage risk: `open`.
   - `remote_enclave`-specific attestation metadata must remain outside the canonical parity
     subject.
25. Shared packager identifier comparability risk: `open`.
   - the v55 evidence surface should require a frozen comparable packager identifier rather
     than free text.
26. Missing explicit deployment-mode source risk: `open`.
   - `remote_enclave` mode must fail closed when no explicit deployment-mode source is
     supplied rather than inheriting defaults or prior state.
27. Remote-enclave packaging hash-chain incompleteness risk: `open`.
   - closeout evidence should record packaging result and packaging manifest hashes, not only
     paths and provenance booleans.
28. Declared adapter count authority ambiguity risk: `open`.
   - `lane_count = 3 × declared_adapter_count` must derive `declared_adapter_count` from
     `adapter_matrix@1` only.
29. Deployment-modes-covered serialization drift risk: `open`.
   - evidence should freeze `deployment_modes_covered` as the lexicographically sorted exact
     enum list rather than an implementation-defined ordering.
30. Verification-passed semantics drift risk: `open`.
   - `verification_passed` in `v34g` evidence should mean deployment-mode guard suite and
     closeout validation only, not live remote execution release or broader attestation
     semantics.
31. Attestation-binding-field scope ambiguity risk: `open`.
   - `attestation_binding_fields_verified` should refer only to the current v55 attestation
     prerequisite set and ideally expose the exact verified fields.

## Recommended Thin Slice

1. Treat `v55` as a remote-enclave deployment-mode baseline only.
   - expand deployment mode enum
   - add deterministic remote-enclave packaging artifacts
2. Freeze authority to current packaging/matrix/attestation surfaces only.
   - reuse `taskpack_ux_packaging_manifest@1`
   - reuse `adapter_matrix@1` / `adapter_matrix_parity_report@1`
   - reuse the closed `V34-E` singleton attestation posture
3. Keep scope intentionally local and narrow.
   - local artifact ingestion only
  - no transport or job dispatch
  - no provider expansion
  - explicit deployment-mode source required with no defaulting
4. Require exact parity preservation.
  - canonical subtree exact match
  - policy-equivalence exact match
  - noncanonical mode differences fenced to the wrapper surface only
5. Add canonical closeout evidence and guard suites in the same arc.
  - the lane is not real until closeout can prove three-mode parity and non-transport
    posture on `main`
  - mode establishment must fail closed without valid attestation prerequisites
  - closeout evidence should bind result/manifest/provenance/attestation artifacts by hash,
    not by path alone

## Pre-Lock Summary (Machine-Checkable)

```json
{
  "schema": "v55_prelock_edge_summary@1",
  "arc": "vNext+55",
  "target_path": "V34-G",
  "identified_edge_count": 31,
  "recommended_scope": "thin_v34g_remote_enclave_mode_baseline_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "blocking_themes": [
    "deployment_mode_enum_must_expand_explicitly_to_remote_enclave",
    "remote_enclave_packaging_lane_must_be_added",
    "matrix_lane_completeness_must_expand_from_two_to_three_modes",
    "remote_transport_and_job_dispatch_must_remain_forbidden",
    "provider_scope_must_remain_singleton_deterministic_test_enclave",
    "v34e_attestation_contract_must_be_reused_not_bypassed",
    "deployment_mode_selection_must_remain_exact_and_explicit",
    "mode_specific_policy_override_must_remain_forbidden",
    "canonical_subtree_parity_must_remain_exact",
    "noncanonical_divergence_must_stay_inside_frozen_wrapper_scope",
    "packaging_schema_family_must_remain_unforked",
    "canonical_v34g_evidence_slot_must_be_added",
    "stop_gate_schema_family_and_metric_keyset_must_remain_frozen",
    "runtime_and_adapter_surfaces_must_not_expand",
    "provider_id_comparison_must_remain_exact_case_sensitive",
    "remote_enclave_mode_must_fail_closed_without_valid_attestation_prerequisites",
    "deployment_mode_dual_source_conflicts_must_fail_closed",
    "lane_count_must_equal_three_times_declared_adapter_count",
    "remote_enclave_packaging_result_and_manifest_hashes_must_be_recorded_in_closeout_evidence",
    "declared_adapter_count_must_derive_only_from_adapter_matrix_at_1",
    "deployment_mode_source_absence_must_fail_closed",
    "deployment_modes_covered_must_serialize_as_sorted_exact_enum_list",
    "verification_passed_semantics_must_remain_narrow_and_non_overclaiming",
    "attestation_binding_fields_verified_must_refer_only_to_current_v55_prerequisite_set",
    "attestation_metadata_must_not_enter_canonical_parity_subject",
    "shared_packager_identifier_must_be_comparable_not_free_text",
    "three_mode_lane_order_must_be_deterministic",
    "existing_integrated_and_standalone_parity_must_not_regress",
    "closeout_must_prove_non_transport_and_attestation_bound_mode_behavior",
    "v34g_must_not_be_overclaimed_as_general_remote_execution_release"
  ]
}
```

## Recommendation

1. Draft `v55` as a thin `V34-G` baseline over deployment-mode expansion only.
2. Keep live transport, job dispatch, provider expansion, and broader attested execution
   behavior deferred.
3. Require deterministic remote-enclave packaging artifacts and three-mode matrix parity
   proof before treating the lane as acceptable in this arc.
4. Require deterministic `v34g_remote_enclave_mode_evidence@1` before treating the lane as
   closed.
