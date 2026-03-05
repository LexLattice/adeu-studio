# Locked Continuation vNext+46 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 5, 2026 UTC).

Decision basis:

- `vNext+45` (`V33-B`, `T1`/`T2`) is merged on `main` via PR `#238` and PR `#239` with green CI checks.
- `vNext+45` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md` with `all_passed = true`.
- Post-v45 planning baseline remains `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`.
- Selected v46 thin-slice default is deterministic verifier/evidence lane:
  - `V33-C` (auditor/verifier + evidence writer).
- `vNext+46` is constrained to deterministic additive hardening for `V33-C` only:
  - no integrated/standalone UX packaging release (`V33-D`),
  - no stop-gate metric-key expansion release in this arc,
  - no schema-family fork in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v46,
  - v46 keyset must be exactly equal to v45 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v46 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36-v45 continuity guarantees remain frozen as release preconditions:
  - worker-route governance continuity remains authoritative,
  - persistence-release continuity remains authoritative,
  - commitments IR continuity remains authoritative,
  - semantic-source continuity remains authoritative,
  - compiler-core continuity remains authoritative,
  - surface-governance continuity remains authoritative,
  - CI/closeout wiring continuity remains authoritative,
  - additive metric-extension continuity remains authoritative,
  - taskpack contract/compiler continuity remains authoritative,
  - constrained-runner continuity remains authoritative.
- Boundary-release scope lock for v46 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- Taskpack/runner authority continuity lock is frozen:
  - verifier authority derives only from compiled taskpack components and deterministic runner artifacts,
  - free-form repository prose and model natural-language self-claims are non-authoritative for policy decisions.
- Verifier input authority lock is frozen:
  - verifier/evidence writer decisions derive from canonical artifact inputs only,
  - prompt injection/runtime natural-language claims cannot override canonical artifact truth.
- Harness portability boundary lock is frozen:
  - harness kernel must not import `apps/api` application-layer modules directly,
  - provider/runtime bindings in this arc must remain adapter-boundary surfaces only.
- Closeout observability continuity lock is frozen:
  - v46 closeout must include a runtime-observability comparison row against v45 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `U1` Deterministic auditor/verifier + evidence writer MVP (`V33-C`)
2. `U2` Verifier determinism/fail-closed guard suite (`V33-C`)

Out-of-scope note:

- integrated + standalone UX packaging release (`V33-D`) in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- taskpack compiler contract-surface expansion beyond v44 `V33-A` authority in this arc,
- runner execution-surface authority expansion beyond v45 `V33-B` in this arc,
- cryptographic signing/key-management release in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v46)

- v47+ integrated + standalone UX packaging (`V33-D`) under explicit lock text.
- v48+ optional taskpack signing and trust-anchor distribution under explicit lock text.
- v49+ optional matrix-lane parity checks for runner/verifier adapters under explicit lock text.
- v50+ independent zero-trust policy-validation recomputation in verifier lane under explicit lock text.
- v51+ rejection-diagnostic retry-context feeder automation under explicit lock text.
- v52+ remote/enclave attested verifier execution under explicit lock text.

## V45 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md",
  "target": "V33-C",
  "required_continuity_guards": [
    "V31_F_GOVERNANCE_CONTINUITY_GREEN",
    "V31_G_PERSISTENCE_CONTINUITY_GREEN",
    "V32_A_COMMITMENTS_CONTINUITY_GREEN",
    "V32_B_SEMANTIC_SOURCE_CONTINUITY_GREEN",
    "V32_C_COMPILER_CORE_CONTINUITY_GREEN",
    "V32_D_SURFACE_CODEGEN_CONTINUITY_GREEN",
    "V32_E_CI_CLOSEOUT_CONTINUITY_GREEN",
    "V32_F_METRIC_EXTENSION_CONTINUITY_GREEN",
    "V33_A_TASKPACK_CONTINUITY_GREEN",
    "V33_B_RUNNER_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v46.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V33-C Verifier Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v33c_verifier_contract@1",
  "target_arc": "vNext+46",
  "target_path": "V33-C",
  "verifier_authority_inputs": {
    "taskpack_manifest": "required",
    "candidate_change_plan": "required_schema_candidate_change_plan@1",
    "runner_result": "required_schema_taskpack_runner_result@1",
    "runner_provenance": "required_schema_taskpack_runner_provenance@1",
    "policy_rejection_diagnostics": "required_when_policy_validation_failed",
    "verified_result_artifact": "required_schema_taskpack_verification_result@1_for_independent_evidence_writer_rerun"
  },
  "verifier_execution_interface": {
    "kernel_package_authority": "packages/adeu_agent_harness",
    "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
    "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
    "execution_mode_default": "sequential_verify_then_evidence_write",
    "independent_evidence_writer_rerun": "allowed_only_with_prior_verified_result_artifact",
    "independent_evidence_writer_without_verified_result": "forbidden_fail_closed",
    "provider_binding_surface": "adapter_interface_only",
    "apps_api_direct_import": "forbidden_non_v46",
    "input_mode": "artifact_only_non_interactive"
  },
  "verification_policy": {
    "deterministic_env_required": [
      "TZ=UTC",
      "LC_ALL=C",
      "PYTHONHASHSEED=0"
    ],
    "required_cross_checks": [
      "taskpack_manifest_hash_match",
      "candidate_change_plan_hash_match",
      "policy_validation_result_consistency",
      "exit_status_consistency"
    ],
    "hash_match_semantics": "recompute_hash_from_canonical_artifact_payload_and_compare_to_recorded_hash_field",
    "recorded_hash_values_without_recompute": "non_authoritative",
    "policy_validation_recomputation": "forbidden_non_v46",
    "policy_validation_authority": "runner_recorded_result_and_policy_rejection_diagnostics_consistency_only",
    "policy_validation_trust_model": "transitional_runner_record_consistency_verification_only_v46",
    "independent_policy_recompute_deferred": "non_v46",
    "required_validation_phase": "pre_evidence_emit",
    "validation_failure_outcome": "fail_closed_no_evidence_emit",
    "required_violation_channel": "error_only_non_zero_exit",
    "required_violation_warning_downgrade": "forbidden"
  },
  "evidence_writer_policy": {
    "authoritative_source": "EVIDENCE_SLOTS.json_only",
    "writable_schema_allowlist": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v33c_verifier_wiring_evidence@1"
    ],
    "required_closeout_blocks": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v33c_verifier_wiring_evidence@1"
    ],
    "required_slot_fill_policy": "all_required_slots_or_fail_closed",
    "output_root": "artifacts/agent_harness/v46/evidence",
    "deterministic_ordering": "stable_slot_id_then_schema",
    "canonical_serialization_policy": "canonical_json_recursive_required_for_all_evidence_blocks_and_rejection_diagnostics",
    "non_canonical_json_encoder_use": "forbidden_fail_closed",
    "additional_schema_emission": "forbidden_non_v46",
    "missing_or_malformed_slot_payload": "fail_closed"
  },
  "diagnostics_policy": {
    "schema": "v33c_verifier_rejection_diagnostic@1",
    "issue_code_parent_namespace": "AHK[0-9]{4}",
    "issue_code_prefix": "AHK46",
    "issue_code_format": "AHK46[0-9]{2}",
    "issue_code_namespace_mapping": "AHK46xx_is_subset_of_AHK[0-9]{4}",
    "registry_authority_path": "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v46.json",
    "registry_required": true,
    "required_on_verification_failure": true,
    "required_fields": [
      "issue_code",
      "reason",
      "artifact_path",
      "evidence_slot_id",
      "policy_source"
    ],
    "policy_source_enum_v46": [
      "taskpack_manifest",
      "evidence_slots",
      "runner_result",
      "runner_provenance",
      "candidate_change_plan",
      "stop_gate_metrics"
    ],
    "deterministic_ordering": "stable_issue_code_then_artifact_path_then_evidence_slot_id",
    "output_path": "artifacts/agent_harness/v46/rejections"
  },
  "provenance_policy": {
    "run_provenance_schema": "taskpack_verifier_provenance@1",
    "required_fields": [
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verification_result",
      "evidence_bundle_hash",
      "exit_status"
    ],
    "hash_subject_fields": [
      "taskpack_manifest_hash",
      "candidate_change_plan_hash",
      "runner_provenance_hash",
      "verification_result",
      "evidence_bundle_hash",
      "exit_status"
    ],
    "excluded_non_authoritative_fields": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths"
    ],
    "evidence_bundle_hash_subject": {
      "schema": "evidence_bundle_hash_subject@1",
      "definition": "sha256_canonical_json(taskpack_manifest_hash + ordered_evidence_blocks + ordered_rejection_diagnostics_optional)",
      "hash_input_encoding": "canonical_json_only",
      "ordered_evidence_blocks_serialization": "canonical_json_per_block_required",
      "ordered_rejection_diagnostics_serialization": "canonical_json_per_diagnostic_required",
      "ordered_evidence_blocks_membership": "emitted_allowlisted_blocks_only",
      "placeholder_or_non_authoritative_fields_in_hash_subject": "forbidden",
      "ordered_evidence_blocks_ordering": "stable_slot_id_then_schema",
      "ordered_rejection_diagnostics_ordering": "stable_issue_code_then_artifact_path_then_evidence_slot_id"
    },
    "deterministic_hash_profile": "sha256_canonical_json_frozen"
  },
  "stop_gate_continuity_policy": {
    "schema_family": "stop_gate_metrics@1",
    "baseline_metrics_artifact": "artifacts/stop_gate/metrics_v45_closeout.json",
    "metric_key_change": "forbidden",
    "expected_keyset_relation": "exact_set_equality_with_v45",
    "expected_cardinality": 80,
    "cardinality_authority": "metrics_object_keys_only",
    "cardinality_check": "computed_metric_key_cardinality_equals_expected_cardinality_fail_closed"
  },
  "closeout_lint_severity_policy": {
    "required_contract_violations": "error",
    "optional_informational_fields": "warning_allowed_non_blocking",
    "required_violation_channel": "error_only_non_zero_exit",
    "required_error_namespace_warning_channel_use": "forbidden"
  },
  "fail_closed_conditions": [
    "verifier_entrypoint_missing",
    "evidence_writer_entrypoint_missing",
    "verifier_kernel_imports_apps_api_detected",
    "verifier_input_artifact_missing_or_invalid",
    "runner_result_schema_drift",
    "runner_provenance_schema_drift",
    "candidate_change_plan_schema_drift",
    "cross_artifact_hash_mismatch",
    "policy_validation_consistency_mismatch",
    "policy_validation_recomputation_attempt_detected",
    "independent_evidence_writer_without_verified_result_detected",
    "required_evidence_slot_missing",
    "required_evidence_slot_malformed",
    "evidence_writer_schema_allowlist_violation",
    "evidence_bundle_hash_non_canonical_serialization_detected",
    "evidence_writer_non_deterministic_ordering_detected",
    "evidence_bundle_hash_subject_drift",
    "diagnostic_issue_code_prefix_or_registry_drift",
    "diagnostic_policy_source_out_of_enum",
    "verification_failure_without_rejection_diagnostic",
    "rejection_diagnostic_missing_or_malformed",
    "verification_failed_with_partial_evidence_emission",
    "provenance_artifact_missing_or_hash_drift",
    "provenance_hash_subject_contains_nondeterministic_fields",
    "stop_gate_metric_keyset_drift",
    "stop_gate_metric_cardinality_authority_drift",
    "required_contract_violation_reported_as_warning",
    "required_structural_violation_captured_as_warning_channel"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## U1) Deterministic Auditor/Verifier + Evidence Writer MVP (`V33-C`)

### Goal

Introduce deterministic verifier/evidence writer execution that validates runner outputs and emits closeout evidence artifacts only after fail-closed verification passes.

### Scope

- Add deterministic verifier entrypoint:
  - consume canonical runner artifacts and verify schema/integrity/cross-hash consistency,
  - hash-match checks recompute hash from canonical artifact payload and compare against recorded hash fields (recorded values alone are non-authoritative),
  - do not re-run policy validation in v46; verify recorded runner policy result and rejection diagnostics consistency only,
  - independent zero-trust policy recomputation is deferred beyond v46 by lock,
  - fail closed on missing/malformed artifacts or cross-artifact mismatch.
- Add deterministic evidence writer:
  - default control flow is sequential `verify -> evidence_write`,
  - independent evidence-writer reruns are allowed only when a prior verified-result artifact is present and hash-valid,
  - source required slots from `EVIDENCE_SLOTS.json` authority only,
  - emit only allowlisted closeout block schemas in this arc (`runtime_observability_comparison@1`, `metric_key_continuity_assertion@1`, `v33c_verifier_wiring_evidence@1`),
  - canonicalize each evidence block and each rejection diagnostic via frozen `canonical_json` before bundle-hash subject assembly,
  - bundle hash subject includes only actually emitted allowlisted evidence blocks and excludes placeholder/non-authoritative fields,
  - emit canonical closeout evidence payloads with deterministic ordering and canonical hashing,
  - block evidence emission on failed verification.
- Add severity-channel enforcement:
  - required violations must emit error diagnostics with non-zero exit,
  - warning-channel downgrade for required violations is forbidden.
- Preserve stop-gate continuity:
  - no metric-key additions,
  - no schema-family fork.

### Locks

- Verifier-authority lock is frozen:
  - verification authority derives from canonical artifacts only.
- Dual-entrypoint control-flow lock is frozen:
  - default execution order is deterministic `verify -> evidence_write`,
  - evidence writer may run independently only when a prior verified-result artifact is present and hash-valid,
  - independent evidence writer execution without prior verified-result artifact is forbidden and fail closed.
- Cross-hash verification semantics lock is frozen:
  - each `*_hash_match` cross-check recomputes from canonical artifact payload and compares against recorded hash field,
  - recorded hash fields are non-authoritative unless recomputation equality succeeds.
- Verifier-policy-validation boundary lock is frozen:
  - verifier does not recompute policy validation in v46,
  - verifier authority is consistency checking of recorded runner policy outputs and diagnostics only.
- Evidence-slot authority lock is frozen:
  - required evidence slots derive from `EVIDENCE_SLOTS.json` only.
- Evidence-schema allowlist lock is frozen:
  - evidence writer may emit only allowlisted schemas in this arc:
    - `runtime_observability_comparison@1`,
    - `metric_key_continuity_assertion@1`,
    - `v33c_verifier_wiring_evidence@1`.
- Evidence-bundle hash-subject lock is frozen:
  - `evidence_bundle_hash` is computed as canonical hash over ordered evidence blocks plus optional ordered rejection diagnostics under frozen ordering rules.
- Evidence canonical-serialization lock is frozen:
  - all evidence blocks and rejection diagnostics entering bundle-hash subject assembly must be canonicalized with frozen `canonical_json`,
  - non-canonical encoder/coercion paths are forbidden and fail closed.
- Verifier diagnostics-code lock is frozen:
  - v46 verifier diagnostics use prefix `AHK46` only,
  - `AHK46xx` is an arc-scoped subset of global harness namespace `AHK[0-9]{4}`,
  - diagnostic code registry is required and authoritative for v46 verifier diagnostics,
  - `policy_source` is a closed enum in this arc (`taskpack_manifest`, `evidence_slots`, `runner_result`, `runner_provenance`, `candidate_change_plan`, `stop_gate_metrics`).
- Verification-no-bypass lock is frozen:
  - evidence emission is forbidden if deterministic verification fails in any control-flow path.
- Deterministic-ordering lock is frozen:
  - evidence payload and diagnostics ordering is stable and hash-replayable.
- Required-error-channel lock is frozen:
  - required structural/contract violations cannot be downgraded to warnings.
- Stop-gate continuity lock is frozen:
  - `stop_gate_metrics@1` only, no keyset expansion, cardinality remains `80`,
  - cardinality is computed from `metrics` object keys only and must equal `80` fail closed.

### Acceptance

- Verifier rejects malformed/mismatched artifact sets deterministically and fail closed.
- Evidence writer emits byte-identical payloads for identical verified inputs.
- Required verification failures always emit deterministic structured diagnostics and non-zero exit.
- v45-v46 stop-gate metric keysets remain exact-set equal (`80`).
- Verification failures emit no partial closeout evidence payloads (rejections-only artifacts allowed).
- Evidence-bundle hash remains byte-stable across reruns and canonicalization-equivalent runtimes.

## U2) Verifier Determinism/Fail-Closed Guard Suite (`V33-C`)

### Goal

Prove v46 verifier/evidence integration behavior is deterministic, fail-closed, and continuity-preserving.

### Scope

- Add/adjust deterministic tests/guards for:
  - verifier/evidence entrypoint presence and import-boundary isolation,
  - verifier input schema/integrity enforcement,
  - cross-artifact hash-consistency verification,
  - required evidence-slot completeness and malformed-slot detection,
  - deterministic evidence ordering and hash stability across reruns,
  - canonical-serialization enforcement for each evidence block and rejection diagnostic entering hash subject assembly,
  - evidence-bundle hash-subject stability across reruns under frozen ordering rules,
  - verification-failure no-evidence-emission behavior (evidence directory empty or rejections-only),
  - deterministic rejection-diagnostic emission and ordering,
  - diagnostics code-prefix/registry conformance (`AHK46` + authoritative registry),
  - required error-channel enforcement (no warning downgrade),
  - stop-gate keyset continuity and deterministic cardinality assertions (`80`, computed from `metrics` keys only),
  - continuity-preservation assertions for v36-v45 frozen suites.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC`, `LC_ALL=C`, and `PYTHONHASHSEED=0` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v46 tests/guards may not introduce new stop-gate metric keys.
- Required-deterministic-env lock is frozen:
  - v46 guards fail closed if deterministic env contract drifts from `TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`.
- Required-verification-no-bypass lock is frozen:
  - v46 guards fail closed if evidence can emit after verification failure.
- Required-evidence-slot-completeness lock is frozen:
  - v46 guards fail closed if required evidence slots are missing/malformed.
- Required-rejection-diagnostics lock is frozen:
  - v46 guards fail closed if verification failures do not produce deterministic structured diagnostics.
- Required-provenance-hash-subject lock is frozen:
  - v46 guards fail closed if deterministic provenance hash subject includes non-deterministic fields.
- Required-severity-policy lock is frozen:
  - v46 guards fail closed if required violations are emitted as warnings.
- Continuity-preservation lock is frozen:
  - v46 guards fail closed if v36-v45 continuity suites regress.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required verifier wiring and fail-closed assertions are green.
- Verification-failure fixture confirms no partial closeout evidence emission (rejections-only artifacts allowed).
- Fixture `verification_failure_no_evidence_emit` asserts evidence directory empty (or rejections-only) with non-zero exit.
- v36-v45 continuity guard suites remain green under v46 scope.

## Stop-Gate Impact (v46)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80` fail closed.
- v46 closeout must include runtime-observability comparison row against v45 baseline.
- v46 closeout must include verifier wiring evidence block:
  - block schema is docs-only `v33c_verifier_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `verifier_entrypoint`
    - `evidence_writer_entrypoint`
    - `verification_passed`
    - `required_evidence_slots_filled`
    - `required_violation_error_channel_enforced`
    - `provenance_hash`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v45`
    - `notes`

## Error/Exit Policy (v46)

- No new URM error-code family is introduced in this arc.
- Harness diagnostics namespace (`AHK[0-9]{4}`) in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- v46 verifier diagnostics are constrained to `AHK46xx`, which is an arc-scoped subset of `AHK[0-9]{4}`, and must resolve through an authoritative registry.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V33-C deterministic verifier lane + evidence writer MVP`
2. `tests: add v46 verifier determinism and fail-closed guard suite`

## Intermediate Preconditions (for v46 start)

1. v45 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v45 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md`
3. Existing v45 runner entrypoint remains available at v46 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
4. Existing v45 closeout artifacts remain available at v46 start:
   - `artifacts/quality_dashboard_v45_closeout.json`
   - `artifacts/stop_gate/metrics_v45_closeout.json`
   - `artifacts/stop_gate/report_v45_closeout.md`
   - `artifacts/agent_harness/v45/closeout_runner_result_run1.json`
   - `artifacts/agent_harness/v45/closeout_runner_result_run2.json`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v45 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `U1` and `U2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic verifier/evidence writer MVP (`V33-C`) is closed and test-covered.
- v46 closeout evidence includes runtime-observability comparison row against v45 baseline and `v33c_verifier_wiring_evidence@1` block.
- v36-v45 continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
