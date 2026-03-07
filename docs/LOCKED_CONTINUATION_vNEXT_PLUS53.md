# Locked Continuation vNext+53 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md`
- `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 7, 2026 UTC).

## Decision Basis

- `vNext+52` (`V34-D`, `A1`/`A2`) is merged on `main` with green CI checks.
- `vNext+52` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md` marks the advisory `V34-D` retry-context feeder
  baseline as closed and restores eligibility for explicit `V34-E` evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` names `V34-E` as the next deferred family candidate
  after the current local trust-baseline lanes.
- current harness reality is narrower than a full live remote verifier lane:
  - local verifier execution is real and deterministic in
    `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`,
  - V34-A trust-anchor registry and downstream signing handoff are real and deterministic,
  - no released `remote_enclave_attestation@1` artifact exists on `main`,
  - no released `attestation_verification_result@1` artifact exists on `main`,
  - no shared provider-neutral attestation normalizer/validator exists on `main`,
  - no verifier path currently consumes externally supplied attested verifier outputs on
    `main`,
  - deployment mode remains frozen to `adeu_integrated` / `standalone` with singleton
    runtime `local_python_cli`.
- `vNext+53` therefore selects one thin `V34-E` baseline slice only:
  - provider-neutral attestation normalization and validation over externally supplied
    verifier outputs,
  - deterministic `remote_enclave_attestation@1` and
    `attestation_verification_result@1`,
  - exact local-equivalence guard against the current local verifier result under identical
    authoritative inputs,
  - canonical closeout evidence integration plus guard coverage,
  - no live provider adapter, remote job dispatch, or `remote_enclave` deployment-mode
    release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v53,
  - v53 keyset must be exactly equal to v52 keyset,
  - baseline derived cardinality at v53 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v53 is explicit and narrow:
  - this arc authorizes one `L2-candidate` attested verifier-ingestion lane only,
  - no governance or persistence authority release is authorized in this arc,
  - no remote execution transport, remote job dispatch, or `remote_enclave`
    deployment-mode release is authorized in this arc.
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
- `V34-E` release-shape lock for v53 is frozen:
  - this arc is an attested verifier-result ingestion and evidence slice only,
  - provider-specific evidence is non-authoritative until normalized into the provider-neutral
    attestation schema,
  - local verifier equivalence remains required in this arc,
  - no live provider adapter, network transport, remote job dispatch, or deployment-mode
    expansion is authorized in this arc,
  - no packaging, matrix, retry-context, or policy semantics may be redefined in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `B1` Shared provider-neutral attestation normalizer/validator + deterministic validation
   result baseline (`V34-E`)
2. `B2` Canonical attestation evidence + exact local-equivalence guard suite (`V34-E`)

Out-of-scope note:

- live remote verifier provider adapters in this arc,
- network transport or remote job dispatch in this arc,
- remote verifier execution without exact local-equivalence comparison in this arc,
- attestation trust-anchor system fork or parallel registry in this arc,
- `remote_enclave` deployment mode expansion (`V34-G`) in this arc,
- standalone integrity self-verification (`V34-F`) in this arc,
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

## Deferred Follow-on Candidates (Non-v53)

- v54+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock
  text.
- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.
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

## V52 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md",
  "target": "V34-E-baseline",
  "required_continuity_guards": [
    "V34_D_A1_RETRY_CONTEXT_FEEDER_GREEN",
    "V34_D_A2_RETRY_CONTEXT_EVIDENCE_GREEN"
  ],
  "expected_relation": "v52_retry_context_baseline_and_closeout_contracts_remain_frozen_while_v34e_attested_verifier_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v53.
- this narrowed machine-checkable consumption block is v52-local only and does not weaken the
  global continuity locks declared above; v36-v52 baseline continuity remains in force for
  the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-E Attested Verifier Contract (Machine-Checkable)

```json
{
  "schema": "v34e_attested_verifier_contract@1",
  "target_arc": "vNext+53",
  "target_path": "V34-E",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "candidate_change_plan_hash": "required",
    "runner_provenance_schema": "taskpack_runner_provenance@1",
    "verification_result_schema": "shared_schema_contract_for_local_and_attested_outputs_authority_comes_from_explicit_hashed_artifacts_only",
    "signature_verification_result_schema": "signature_verification_result@1",
    "trust_anchor_registry_schema": "taskpack_trust_anchor_registry@1",
    "v34a_handoff_completion_contract": "required_frozen_precondition",
    "v34b_matrix_baseline_contract": "required_frozen_precondition",
    "v34c_policy_recompute_contract": "required_frozen_precondition",
    "v34d_retry_context_contract": "required_frozen_precondition"
  },
  "attestation_scope_requirements": {
    "remote_enclave_attestation_schema": "remote_enclave_attestation@1",
    "attestation_verification_result_schema": "attestation_verification_result@1",
    "shared_attestation_validator_required": true,
    "attested_subject_schema": "taskpack_verification_result@1",
    "input_mode": "explicit_local_artifact_ingestion_only_missing_required_paths_fail_closed",
    "attestation_authority_source_policy": "provider_specific_evidence_must_be_normalized_to_provider_neutral_schema_before_validation_no_provider_specific_fields_as_authority_prior_to_normalization",
    "provider_id_policy": "closed_singleton_test_provider_for_v53",
    "provider_id_comparison_policy": "exact_case_sensitive_equality_against_deterministic_test_enclave",
    "provider_id_enum": [
      "deterministic_test_enclave"
    ],
    "provider_adapter_expansion_forbidden": true,
    "attestation_trust_anchor_source_policy": "reuse_v34a_taskpack_trust_anchor_registry_single_source_no_parallel_trust_anchor_system",
    "verification_reference_time_utc_policy": "required_explicit_input_no_wall_clock_default",
    "normalized_claim_fields": [
      "provider_id",
      "attestation_key_id",
      "algorithm",
      "verification_reference_time_utc",
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verified_result_hash",
      "opaque_provider_evidence_hash"
    ],
    "runner_provenance_hash_policy": "sha256_over_full_taskpack_runner_provenance_at_1_canonical_json_artifact",
    "opaque_provider_evidence_hash_policy": "audit_only_binding_to_raw_provider_blob_not_part_of_exact_local_equivalence_subject",
    "normalized_claim_duplicate_or_conflict_policy": "duplicate_or_conflicting_normalized_claims_after_normalization_to_provider_neutral_schema_forbidden_fail_closed",
    "provider_specific_claim_projection_policy": "no_authority_beyond_normalized_claim_fields_in_v53",
    "attestation_binding_fields": [
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verified_result_hash",
      "trust_anchor_registry_hash",
      "verification_reference_time_utc",
      "attestation_key_id",
      "algorithm",
      "provider_id",
      "attestation_verified"
    ],
    "attestation_verified_must_equal_true": true,
    "attested_verified_result_schema_validation_required": true,
    "local_equivalence_required": true,
    "current_local_verification_recompute_required": true,
    "current_local_verification_source_policy": "must_be_materialized_in_current_v53_flow_from_same_authoritative_inputs_not_reused_from_stale_prior_artifact",
    "current_local_verification_materialization_failure_outcome": "fail_closed_cannot_establish_local_equivalence",
    "local_equivalence_binding_fields_verified": [
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verified_result_hash"
    ],
    "local_equivalence_subject_fields": [
      "verified_result_hash"
    ],
    "local_equivalence_subject_policy": "exact_match_subject_is_verified_result_hash_only_binding_fields_separately_guard_input_identity_and_current_local_result_must_be_materialized_in_current_v53_flow_from_same_authoritative_inputs",
    "remote_transport_or_job_dispatch_forbidden": true,
    "deployment_mode_expansion_forbidden": true,
    "replay_nondeterministic_fields_forbidden": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths",
      "network_endpoint",
      "random_nonce"
    ]
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34e_attestation_evidence@1",
    "canonical_closeout_evidence_required": true,
    "verification_passed_policy": "true_means_attestation_normalization_validation_local_equivalence_guards_and_closeout_validation_passed_not_policy_validation_packaging_validation_or_remote_job_success",
    "shared_attestation_validator_identifier_policy": "frozen_module_function_path_or_registry_key_no_free_text",
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "attestation_entrypoint",
      "shared_attestation_validator_used",
      "shared_attestation_validator_identifier",
      "shared_attestation_validator_identifier_policy",
      "local_verifier_entrypoint",
      "remote_enclave_attestation_path",
      "remote_enclave_attestation_hash",
      "attested_verified_result_path",
      "attested_verified_result_hash",
      "local_verified_result_path",
      "local_verified_result_hash",
      "attestation_verification_result_path",
      "attestation_verification_result_hash",
      "provider_id",
      "provider_id_closed_singleton_enforced",
      "provider_id_comparison_policy",
      "attestation_trust_anchor_registry_reused",
      "runner_provenance_hash_policy",
      "attestation_verified_required",
      "input_mode_artifact_ingestion_only",
      "attested_verified_result_schema_validated",
      "current_local_verification_recomputed",
      "current_local_verification_materialization_failure_fails_closed",
      "local_equivalence_required",
      "local_equivalence_subject_fields_verified",
      "local_equivalence_binding_fields_verified",
      "local_equivalence_verified",
      "opaque_provider_evidence_hash_audit_only",
      "normalized_claim_conflicts_forbidden",
      "remote_transport_or_job_dispatch_forbidden",
      "deployment_mode_expansion_forbidden",
      "verification_passed",
      "verification_passed_policy",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v52",
      "notes"
    ]
  },
  "test_requirements": {
    "attestation_verification_result_deterministic_for_identical_inputs": true,
    "provider_neutral_normalization_required": true,
    "non_normalized_provider_evidence_forbidden": true,
    "provider_id_outside_closed_singleton_rejected": true,
    "attestation_verified_false_rejected": true,
    "attested_verified_result_schema_validation_required": true,
    "local_equivalence_match_required_for_acceptance": true,
    "local_equivalence_mismatch_fail_closed": true,
    "current_local_verification_recomputed_before_equivalence": true,
    "current_local_verification_materialization_failure_fails_closed": true,
    "duplicate_or_conflicting_normalized_claims_rejected": true,
    "artifact_ingestion_only_enforced": true,
    "remote_transport_not_required_or_used": true
  },
  "fail_closed_conditions": [
    "remote_enclave_attestation_missing_from_attested_path",
    "attestation_verification_result_missing_after_validation",
    "provider_specific_evidence_used_as_authority_without_normalization",
    "provider_id_outside_closed_singleton_accepted",
    "attestation_verified_false_accepted",
    "attested_verified_result_not_schema_valid_before_hash_equivalence",
    "parallel_attestation_trust_anchor_system_accepted",
    "duplicate_or_conflicting_normalized_claims_accepted",
    "attested_verified_result_hash_mismatch_accepted",
    "stale_local_verified_result_reused_for_equivalence",
    "attested_verified_result_without_local_equivalence_accepted",
    "non_artifact_ingestion_source_used_for_v53_attestation_input",
    "remote_transport_or_job_dispatch_released_in_v53",
    "deployment_mode_expansion_released_in_v53",
    "attestation_evidence_missing_from_closeout"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## B1) Shared Provider-Neutral Attestation Normalizer/Validator + Deterministic Validation Result Baseline (`V34-E`)

### Goal

Make `V34-E` real as a provider-neutral attested verifier-ingestion baseline over canonical
verifier outputs rather than ad hoc remote-proof handling.

### Scope

- extract or define a shared provider-neutral attestation normalizer/validator over
  externally supplied verifier outputs;
- emit deterministic `remote_enclave_attestation@1` and
  `attestation_verification_result@1`;
- freeze `provider_id` to a singleton deterministic test-provider surface in this arc;
- bind attestation validation to the existing trust-anchor registry and canonical verifier
  result hashes.

### Locks

- v53 must not widen provider scope beyond the singleton `deterministic_test_enclave`
  surface.
- attestation input authority must derive only from:
  - provider-neutral normalized attestation payload,
  - canonical `taskpack_verification_result@1`,
  - canonical runner provenance,
  - existing V34-A trust-anchor registry and explicit verification reference time.
- `taskpack_verification_result@1` is the shared schema contract for both local and
  attested verifier outputs; authority comes from the specific hashed artifacts named in the
  attestation scope and closeout evidence blocks, not from a generic preexisting verifier
  artifact.
- all attestation inputs in v53 must be supplied as explicit local artifact paths; missing
  required attestation, verifier-result, trust-anchor, or provenance paths fail closed.
- provider-specific raw evidence is non-authoritative until normalized into
  `remote_enclave_attestation@1`.
- `runner_provenance_hash` means the sha256 over the canonical JSON bytes of the full frozen
  `taskpack_runner_provenance@1` artifact, not a subset or projection.
- `provider_id` comparison is exact, case-sensitive equality against the frozen singleton
  value `deterministic_test_enclave`.
- `attestation_verified` must be present and equal `true`; field presence alone is
  insufficient for acceptance.
- `opaque_provider_evidence_hash` is audit-only binding to the raw provider evidence blob and
  is not part of the exact local-equivalence subject in v53.
- duplicate or conflicting normalized claims after normalization into the provider-neutral
  schema are invalid and fail closed.
- no parallel trust-anchor system is authorized in this arc.
- no remote transport, network dispatch, or remote job orchestration is authorized in this
  arc.
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- identical inputs produce deterministic `remote_enclave_attestation@1` bytes across reruns;
- identical inputs produce deterministic `attestation_verification_result@1` bytes across
  reruns;
- provider ids outside the closed singleton surface fail closed;
- non-normalized provider evidence is rejected fail closed.

## B2) Canonical Attestation Evidence + Exact Local-Equivalence Guard Suite (`V34-E`)

### Goal

Make the attestation lane auditable while ensuring attested verifier output stays exactly
equivalent to the current local verifier output under identical authoritative inputs.

### Scope

- require exact local-equivalence comparison between attested verified result and current
  local verified result under identical authoritative inputs;
- add canonical closeout evidence for the v34e attestation lane;
- add deterministic guard coverage for:
  - provider-neutral normalization,
  - singleton provider enforcement,
  - local-equivalence mismatch failure,
  - prohibition on remote transport/job dispatch in this arc;
- integrate the attestation lane into canonical closeout evidence without expanding
  deployment mode or remote transport authority.

### Locks

- exact local-equivalence is required for acceptance in v53.
- the current local verifier result used for equivalence must be materialized in the current
  v53 flow from the same authoritative inputs; reusing a stale prior local verifier artifact
  is forbidden.
- if the current local verifier result cannot be materialized in the current v53 flow,
  equivalence cannot be established and acceptance fails closed.
- externally supplied attested verifier output must validate against
  `taskpack_verification_result@1` before its hash is treated as authoritative for the
  equivalence check.
- attested verified results must not be accepted in this arc without a matching current local
  verifier result hash.
- the exact local-equivalence subject is the verified-result hash only; the separate binding
  fields guard input identity and must also match under the frozen v53 contract.
- closeout proof must distinguish between:
  - `remote_enclave_attestation@1`,
  - `attestation_verification_result@1`,
  - attested `taskpack_verification_result@1`,
  - local `taskpack_verification_result@1`,
  - docs-side `v34e_attestation_evidence@1`.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v34e_attestation_evidence@1` block;
- local-equivalence mismatch fails closed;
- no live transport or deployment-mode expansion is introduced in this arc;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v53)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v53 closeout must include runtime-observability comparison row against v52 baseline.
- v53 closeout must include metric-key continuity assertion against v52 baseline.
- v53 closeout must include attestation evidence block:
  - block schema is docs-only `v34e_attestation_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `attestation_entrypoint`
    - `shared_attestation_validator_used`
    - `shared_attestation_validator_identifier`
    - `local_verifier_entrypoint`
    - `remote_enclave_attestation_path`
    - `remote_enclave_attestation_hash`
    - `attested_verified_result_path`
    - `attested_verified_result_hash`
    - `local_verified_result_path`
    - `local_verified_result_hash`
    - `attestation_verification_result_path`
    - `attestation_verification_result_hash`
    - `provider_id`
    - `provider_id_closed_singleton_enforced`
    - `provider_id_comparison_policy`
    - `attestation_trust_anchor_registry_reused`
    - `runner_provenance_hash_policy`
    - `attestation_verified_required`
    - `input_mode_artifact_ingestion_only`
    - `attested_verified_result_schema_validated`
    - `current_local_verification_recomputed`
    - `current_local_verification_materialization_failure_fails_closed`
    - `local_equivalence_required`
    - `local_equivalence_subject_fields_verified`
    - `local_equivalence_binding_fields_verified`
    - `local_equivalence_verified`
    - `opaque_provider_evidence_hash_audit_only`
    - `normalized_claim_conflicts_forbidden`
    - `remote_transport_or_job_dispatch_forbidden`
    - `deployment_mode_expansion_forbidden`
    - `verification_passed`
    - `verification_passed_policy`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v52`
    - `notes`

## Error/Exit Policy (v53)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v53 introduces new attestation-specific harness diagnostics, they must be constrained to
  an authoritative `AHK53xx` registry and remain error-only with non-zero exit behavior.
- If v53 introduces new attestation diagnostics, deterministic issue ordering must sort by
  `(issue_code, provider_id, verified_result_hash, artifact_path)`.
- for attestation exact-input subjects, `provider_id` serializes from the frozen singleton
  enum and `verified_result_hash` remains sha256-typed from the frozen verifier contract.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34e attestation validation baseline`
2. `tests: add v34e equivalence and evidence guards`

## Intermediate Preconditions (for v53 start)

1. v52 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v52 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md`
3. Existing v52 retry-context baseline remains available at v53 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/retry_context.py`
   - `artifacts/agent_harness/v52/evidence_inputs/v34d_retry_context_evidence_v52.json`
4. Existing local verifier/signing/closeout evidence surfaces remain available at v53 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
5. Existing v52 closeout artifacts remain available at v53 start:
   - `artifacts/quality_dashboard_v52_closeout.json`
   - `artifacts/stop_gate/metrics_v52_closeout.json`
   - `artifacts/stop_gate/report_v52_closeout.md`
   - `artifacts/agent_harness/v52/evidence_inputs/runtime_observability_comparison_v52.json`
   - `artifacts/agent_harness/v52/evidence_inputs/metric_key_continuity_assertion_v52.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No additional deployment mode or live remote transport authority beyond the v52 baseline
   is introduced in this arc.

## Exit Criteria (Draft)

- `B1` and `B2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-E` attested verifier baseline remains provider-neutral, deterministic, and exact
  local-equivalence checked without widening into live remote transport or deployment-mode
  expansion.
- v53 closeout evidence includes runtime-observability comparison row against v52 baseline,
  metric-key continuity assertion against v52 baseline, and `v34e_attestation_evidence@1`.
- `remote_enclave_attestation@1` and `attestation_verification_result@1` are deterministic
  under identical inputs.
- local-equivalence mismatch fails closed.
- v36-v52 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
