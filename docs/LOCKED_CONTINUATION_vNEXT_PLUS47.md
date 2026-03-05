# Locked Continuation vNext+47 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 5, 2026 UTC).

Decision basis:

- `vNext+46` (`V33-C`, `U1`/`U2`) is merged on `main` via PR `#240` and PR `#241` with green CI checks.
- `vNext+46` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md` with `all_passed = true`.
- Post-v46 planning baseline remains `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`.
- Selected v47 thin-slice default is deterministic UX surface packaging:
  - `V33-D` (integrated + standalone packaging surfaces over shared harness kernel).
- `vNext+47` is constrained to deterministic additive hardening for `V33-D` only:
  - no stop-gate metric-key expansion release in this arc,
  - no schema-family fork in this arc,
  - no zero-trust policy-validation recomputation release in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v47,
  - v47 keyset must be exactly equal to v46 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v47 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36-v46 continuity guarantees remain frozen as release preconditions:
  - worker-route governance continuity remains authoritative,
  - persistence-release continuity remains authoritative,
  - commitments IR continuity remains authoritative,
  - semantic-source continuity remains authoritative,
  - compiler-core continuity remains authoritative,
  - surface-governance continuity remains authoritative,
  - CI/closeout wiring continuity remains authoritative,
  - additive metric-extension continuity remains authoritative,
  - taskpack contract/compiler continuity remains authoritative,
  - constrained-runner continuity remains authoritative,
  - verifier/evidence-writer continuity remains authoritative.
- Boundary-release scope lock for v47 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- Taskpack/runner/verifier authority continuity lock is frozen:
  - packaging authority derives from canonical taskpack, verified-result, and closeout evidence artifacts only,
  - free-form repository prose and model natural-language self-claims are non-authoritative for policy decisions.
- Packaging mode-identity lock is frozen:
  - integrated and standalone surfaces must consume identical kernel contracts,
  - mode adapters cannot redefine policy semantics.
- Harness portability boundary lock is frozen:
  - harness kernel must not import `apps/api` application-layer modules directly,
  - provider/runtime bindings in this arc must remain adapter-boundary surfaces only.
- Closeout observability continuity lock is frozen:
  - v47 closeout must include a runtime-observability comparison row against v46 canonical baseline.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `W1` Deterministic integrated + standalone UX surface packaging MVP (`V33-D`)
2. `W2` Packaging determinism/policy-equivalence fail-closed guard suite (`V33-D`)

Out-of-scope note:

- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- taskpack/compiler contract-surface expansion beyond v44 `V33-A` authority in this arc,
- runner execution authority expansion beyond v45 `V33-B` in this arc,
- verifier trust-model expansion beyond v46 `V33-C` in this arc,
- cryptographic signing/key-management release in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v47)

- v48+ optional taskpack signing and trust-anchor distribution under explicit lock text.
- v49+ optional matrix-lane parity checks for packaging-mode adapters under explicit lock text.
- v50+ independent zero-trust policy-validation recomputation in verifier lane under explicit lock text.
- v51+ rejection-diagnostic retry-context feeder automation under explicit lock text.
- v52+ remote/enclave attested verifier execution under explicit lock text.
- v53+ standalone bundle integrity self-verification script (`verify_integrity.py`) with deterministic manifest re-hash checks under explicit lock text.
- v54+ optional `remote_enclave` packaging deployment mode under explicit lock text.

## V46 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md",
  "target": "V33-D",
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
    "V33_B_RUNNER_CONTINUITY_GREEN",
    "V33_C_VERIFIER_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v47.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V33-D Packaging Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v33d_packaging_contract@1",
  "target_arc": "vNext+47",
  "target_path": "V33-D",
  "packaging_authority_inputs": {
    "taskpack_manifest": "required",
    "taskpack_required_components": [
      "TASKPACK.md",
      "ACCEPTANCE.json",
      "ALLOWLIST.json",
      "FORBIDDEN.json",
      "COMMANDS.json",
      "EVIDENCE_SLOTS.json",
      "taskpack_manifest.json"
    ],
    "verified_result_artifact": "required_schema_taskpack_verification_result@1",
    "evidence_bundle_artifact": "required_schema_taskpack_closeout_evidence_bundle@1",
    "verifier_provenance_artifact": "required_schema_taskpack_verifier_provenance@1",
    "runtime_observability_comparison": "required_schema_runtime_observability_comparison@1",
    "metric_key_continuity_assertion": "required_schema_metric_key_continuity_assertion@1"
  },
  "packaging_execution_interface": {
    "kernel_package_authority": "packages/adeu_agent_harness",
    "integrated_entrypoint": "python -m adeu_agent_harness.package_ux_integrated",
    "standalone_entrypoint": "python -m adeu_agent_harness.package_ux_standalone",
    "packaging_manifest_schema": "taskpack_ux_packaging_manifest@1",
    "deployment_mode_key": "deployment_mode",
    "deployment_modes": [
      "adeu_integrated",
      "standalone"
    ],
    "mode_selection_policy": "deterministic_single_match_fail_closed",
    "mode_match_predicate": "exact_case_sensitive_deployment_mode_equality",
    "deployment_mode_source": "explicit_cli_flag_only_v47",
    "deployment_mode_cli_flag": "--deployment-mode",
    "subprocess_mode_propagation_policy": "required_explicit_deployment_mode_flag_forwarding_no_env_override_non_v47",
    "subprocess_delegation_definition": "any_subprocess_invocation_of_packaging_related_entrypoints",
    "unrelated_tool_subprocesses": "allowed_non_authoritative_for_mode_selection",
    "implicit_default_mode": "forbidden_non_v47",
    "artifact_based_mode_selection": "forbidden_non_v47",
    "deployment_mode_env_override": "forbidden_non_v47",
    "mode_adapter_surface": "adapter_interface_only",
    "apps_api_direct_import_for_kernel": "forbidden_non_v47",
    "input_mode": "artifact_only_non_interactive",
    "dry_run_flag": "--dry-run",
    "dry_run_mode": "model_free_packaging_preview_required",
    "packaging_output_root": "artifacts/agent_harness/v47/packaging"
  },
  "packaging_policy": {
    "authoritative_instruction_source": "taskpack_declared_context_blocks_and_packaging_contract_only",
    "mode_contract_identity_required": true,
    "mode_specific_policy_override": "forbidden_non_v47",
    "packaging_output_boundary": {
      "parity_domain": "canonical_json_artifact_subjects_only",
      "bundle_domain": "non_canonical_packaged_files_may_differ_by_mode_only_when_fully_manifest_described_and_policy_semantics_preserved",
      "bundle_domain_policy_semantics_effect": "forbidden_non_v47"
    },
    "adapter_input_path_normalization_policy": "repo_relative_posix_dot_segment_collapsed_before_canonicalization_required",
    "os_native_path_separator_in_canonical_subjects": "forbidden_fail_closed",
    "required_validation_phase": "pre_package_emit",
    "validation_control_flow": "single_package_gate_no_bypass_even_on_exception_paths",
    "validation_failure_outcome": "fail_closed_no_package_emit"
  },
  "parity_policy": {
    "artifact_parity_subjects": [
      "taskpack_manifest.json",
      "ACCEPTANCE.json",
      "ALLOWLIST.json",
      "FORBIDDEN.json",
      "COMMANDS.json",
      "EVIDENCE_SLOTS.json",
      "taskpack_verification_result@1",
      "taskpack_closeout_evidence_bundle@1",
      "taskpack_verifier_provenance@1",
      "taskpack_ux_packaging_manifest@1"
    ],
    "artifact_parity_relation": "byte_identical_for_canonical_json_subjects",
    "canonical_artifact_subject_bytes": "canonical_json_frozen_profile_only",
    "schema_typed_artifact_pre_parity_validation_required": true,
    "schema_typed_artifact_validation_failure_outcome": "fail_closed",
    "policy_equivalence_subjects": [
      "issue_code_set",
      "required_evidence_slots_filled",
      "allowlist_violations",
      "forbidden_effects_detected"
    ],
    "policy_equivalence_extraction_sources": [
      "taskpack_verification_result@1",
      "taskpack_closeout_evidence_bundle@1"
    ],
    "policy_equivalence_field_types": {
      "issue_code_set": "set_of_strings_canonicalized_as_sorted_unique_array",
      "required_evidence_slots_filled": "boolean",
      "allowlist_violations": "set_of_normalized_repo_relative_posix_paths_canonicalized_as_sorted_unique_array",
      "forbidden_effects_detected": "boolean"
    },
    "policy_equivalence_inference_from_repo_state": "forbidden_non_v47",
    "policy_equivalence_relation": "exact_set_equality_or_exact_boolean_match_per_field",
    "mode_variant_output_difference_outside_allowed_surfaces": "forbidden_non_v47"
  },
  "packaging_manifest_policy": {
    "schema": "taskpack_ux_packaging_manifest@1",
    "authoritative_for_bundle_inventory": true,
    "required_fields": [
      "schema",
      "deployment_mode",
      "authority_artifact_hashes",
      "emitted_files",
      "packaging_bundle_hash"
    ],
    "emitted_files_entry_fields": [
      "path",
      "sha256"
    ],
    "emitted_files_path_normalization": "repo_relative_posix_dot_segment_collapsed_required",
    "emitted_files_ordering": "stable_path_ascending",
    "packaging_bundle_hash_definition": "sha256_canonical_json(ordered_emitted_files_records)",
    "packaging_bundle_hash_subject_fields": [
      "path",
      "sha256"
    ],
    "packaging_bundle_hash_subject_includes_path_and_sha256_fields": true,
    "packaging_bundle_hash_subject_path_form": "normalized_repo_relative_posix_dot_segment_collapsed_path_only",
    "packaging_bundle_hash_subject_excludes_non_authoritative_fields": true
  },
  "diagnostics_policy": {
    "schema": "v33d_packaging_rejection_diagnostic@1",
    "issue_code_parent_namespace": "AHK[0-9]{4}",
    "issue_code_prefix": "AHK47",
    "issue_code_format": "AHK47[0-9]{2}",
    "registry_authority_path": "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json",
    "registry_required": true,
    "required_on_packaging_failure": true,
    "required_fields": [
      "issue_code",
      "reason",
      "artifact_path",
      "deployment_mode",
      "policy_source"
    ],
    "policy_source_enum_v47": [
      "taskpack_manifest",
      "verified_result",
      "evidence_bundle",
      "verifier_provenance",
      "packaging_manifest",
      "stop_gate_metrics"
    ],
    "artifact_path_normalization": "repo_relative_posix_dot_segment_collapsed_required",
    "ordering_artifact_path_subject": "normalized_artifact_path",
    "deterministic_ordering": "stable_issue_code_then_artifact_path_then_deployment_mode_then_policy_source",
    "output_path": "artifacts/agent_harness/v47/rejections"
  },
  "provenance_policy": {
    "run_provenance_schema": "taskpack_packaging_provenance@1",
    "required_fields": [
      "taskpack_manifest_hash",
      "verified_result_hash",
      "evidence_bundle_hash",
      "deployment_mode",
      "parity_result",
      "exit_status"
    ],
    "hash_subject_fields": [
      "taskpack_manifest_hash",
      "verified_result_hash",
      "evidence_bundle_hash",
      "deployment_mode",
      "parity_result",
      "exit_status"
    ],
    "excluded_non_authoritative_fields": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths"
    ],
    "deterministic_hash_profile": "sha256_canonical_json_frozen"
  },
  "closeout_doc_policy": {
    "decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md",
    "required_json_blocks": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v33d_packaging_wiring_evidence@1"
    ]
  },
  "stop_gate_continuity_policy": {
    "schema_family": "stop_gate_metrics@1",
    "baseline_metrics_artifact": "artifacts/stop_gate/metrics_v46_closeout.json",
    "metric_key_change": "forbidden",
    "expected_keyset_relation": "exact_set_equality_with_v46",
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
    "integrated_entrypoint_missing",
    "standalone_entrypoint_missing",
    "packaging_kernel_imports_apps_api_detected",
    "packaging_input_artifact_missing_or_invalid",
    "verified_result_schema_drift",
    "evidence_bundle_schema_drift",
    "verifier_provenance_schema_drift",
    "deployment_mode_unknown",
    "deployment_mode_resolution_ambiguous",
    "deployment_mode_non_exact_match_detected",
    "deployment_mode_source_invalid",
    "deployment_mode_implicit_default_detected",
    "deployment_mode_artifact_derived_selection_detected",
    "subprocess_deployment_mode_flag_missing",
    "deployment_mode_env_override_detected",
    "subprocess_delegation_classification_drift",
    "mode_contract_identity_mismatch",
    "mode_specific_policy_override_detected",
    "pre_package_validation_bypass_detected",
    "pre_package_validation_exception_path_bypass_detected",
    "artifact_parity_drift_detected",
    "artifact_parity_schema_validation_failed",
    "policy_equivalence_drift_detected",
    "policy_equivalence_field_typing_drift",
    "packaging_output_boundary_violation",
    "package_manifest_missing_or_malformed",
    "packaging_manifest_bundle_inventory_missing_or_malformed",
    "packaging_bundle_hash_subject_field_omission_detected",
    "packaging_manifest_bundle_hash_subject_drift",
    "canonical_subject_path_normalization_drift",
    "policy_equivalence_extraction_source_drift",
    "packaging_failure_without_rejection_diagnostic",
    "diagnostic_artifact_path_normalization_drift",
    "rejection_diagnostic_ordering_tie_break_drift",
    "rejection_diagnostic_missing_or_malformed",
    "packaging_provenance_artifact_missing_or_hash_drift",
    "packaging_provenance_hash_subject_contains_nondeterministic_fields",
    "stop_gate_metric_keyset_drift",
    "stop_gate_metric_cardinality_authority_drift",
    "required_contract_violation_reported_as_warning",
    "required_structural_violation_captured_as_warning_channel"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## W1) Deterministic Integrated + Standalone UX Packaging MVP (`V33-D`)

### Goal

Introduce deterministic packaging surfaces that expose the same harness kernel contracts in integrated and standalone modes without policy-semantic drift.

### Scope

- Add deterministic packaging entrypoints:
  - integrated mode entrypoint,
  - standalone mode entrypoint,
  - both consume canonical taskpack + verified-result + evidence artifacts only.
- Add deployment-mode selection enforcement:
  - deployment mode source is explicit CLI flag input only (`--deployment-mode`) in v47,
  - subprocess delegation means any `subprocess.*` invocation of packaging-related entrypoints,
  - if packaging delegates to subprocesses, the explicit `--deployment-mode` flag must be forwarded (no env override lane in v47),
  - unrelated tool subprocesses are allowed but must not influence mode selection authority,
  - exact case-sensitive `deployment_mode` matching only,
  - fail closed on unknown/ambiguous/non-exact mode selection.
- Add packaging manifest emission:
  - emit `taskpack_ux_packaging_manifest@1` with mode + authority artifact hashes + emitted-file inventory (`path`, `sha256`) + `packaging_bundle_hash`,
  - emitted-file inventory paths are normalized repo-relative posix paths with dot-segment collapse,
  - `packaging_bundle_hash` is the canonical hash over ordered emitted-file records and includes both normalized `path` bytes and `sha256` bytes per record,
  - canonical JSON only, deterministic ordering only.
- Add deterministic parity verification across modes:
  - normalize adapter-origin paths to repo-relative posix form with dot-segment collapse before any canonicalization/parity subject assembly,
  - enforce byte-identity for canonical artifact subjects as frozen-profile canonical JSON bytes only,
  - require schema-typed artifact validation before parity comparison,
  - enforce frozen policy-equivalence subjects extracted from `taskpack_verification_result@1` and `taskpack_closeout_evidence_bundle@1` only,
  - enforce frozen policy-equivalence field types:
    - `issue_code_set` as set of strings (canonical sorted unique array),
    - `required_evidence_slots_filled` as boolean,
    - `allowlist_violations` as set of normalized repo-relative posix paths (canonical sorted unique array),
    - `forbidden_effects_detected` as boolean,
  - enforce packaging output boundary:
    - parity domain is canonical JSON artifact subjects only,
    - non-canonical packaged bundle outputs may differ by mode only when fully manifest-described and policy semantics are unchanged.
- Preserve stop-gate continuity:
  - no metric-key additions,
  - no schema-family fork.

### Locks

- Packaging-authority lock is frozen:
  - packaging authority derives from canonical artifacts only.
- Mode-identity lock is frozen:
  - integrated and standalone modes consume identical kernel contracts,
  - mode adapters cannot redefine policy semantics.
- Mode-selection lock is frozen:
  - mode selection is deterministic by exact case-sensitive `deployment_mode` equality only.
- Deployment-mode source lock is frozen:
  - `deployment_mode` input source is explicit CLI flag only in v47,
  - implicit defaults and artifact-derived mode selection are forbidden.
- Deployment-mode propagation lock is frozen:
  - subprocess delegation includes any `subprocess.*` invocation of packaging-related entrypoints,
  - required subprocess delegations must preserve explicit `--deployment-mode` forwarding,
  - unrelated tool subprocesses may run but are non-authoritative for mode selection,
  - env-based deployment-mode overrides are forbidden in v47.
- Pre-package validation lock is frozen:
  - packaging parity/policy-equivalence checks must pass before package emit.
- Pre-package no-bypass lock is frozen:
  - package emit paths must pass through one deterministic validation gate under both normal and exception/error control flow.
- Packaging-output boundary lock is frozen:
  - parity domain is canonical JSON artifact subjects only,
  - non-canonical packaged bundle outputs may differ by mode only when declared in deterministic manifest inventory and policy semantics remain invariant.
- Artifact-parity lock is frozen:
  - canonical artifact parity subjects must remain byte-identical across modes as frozen-profile canonical JSON bytes,
  - schema-typed artifact validation is required before parity comparison.
- Policy-equivalence lock is frozen:
  - policy-equivalence subjects remain frozen and must be exact-equal across modes.
- Policy-equivalence field-typing lock is frozen:
  - policy-equivalence subjects must preserve frozen field typing/encoding rules for set/boolean subjects.
- Policy-equivalence extraction-source lock is frozen:
  - policy-equivalence subjects are extracted from `taskpack_verification_result@1` and `taskpack_closeout_evidence_bundle@1` only,
  - repository-state inference for policy-equivalence is forbidden.
- Packaging-manifest bundle-authority lock is frozen:
  - `taskpack_ux_packaging_manifest@1` is authoritative for emitted bundle inventory and `packaging_bundle_hash`,
  - emitted file list and bundle hash subject must be deterministic and canonicalized,
  - `packaging_bundle_hash` subject includes both normalized `path` and `sha256` fields for each emitted-file record.
- Anti-injection lock is frozen:
  - repository content and model natural-language claims cannot override packaging authority artifacts.
- Canonical-subject path-normalization lock is frozen:
  - adapter-origin paths must be normalized to repo-relative posix dot-segment-collapsed form before canonicalization and hash-subject assembly.
- Rejection-diagnostics lock is frozen:
  - packaging failures must emit deterministic structured rejection diagnostics artifacts,
  - `artifact_path` must be normalized to repo-relative posix path with dot-segment collapse before sorting/emission,
  - deterministic ordering includes `policy_source` as final tie-break,
  - missing or malformed diagnostics on required failure is invalid and fail closed.
- Provenance hash-subject lock is frozen:
  - deterministic hashed provenance excludes non-deterministic environment/time/host fields.
- Severity lock is frozen:
  - required violations are errors and fail closed.

### Acceptance

- Integrated and standalone modes emit byte-identical canonical artifact subjects for identical input bytes.
- Schema-typed canonical artifact subjects pass schema validation before parity comparison.
- Policy-equivalence subjects are exact-equal across both modes.
- Unknown/ambiguous/invalid mode selections fail closed deterministically.
- Packaging manifests are deterministic and authoritative for emitted bundle inventory and `packaging_bundle_hash`.
- Packaging provenance artifacts are deterministic and hash-stable across reruns.

## W2) Packaging Determinism/Policy-Equivalence Guard Suite (`V33-D`)

### Goal

Prove v47 packaging behavior is deterministic, policy-equivalent across modes, fail-closed, and continuity-preserving.

### Scope

- Add/adjust deterministic tests/guards for:
  - integrated/standalone packaging entrypoint presence and adapter-boundary isolation,
  - packaging input schema/integrity enforcement,
  - deterministic mode selection checks (unknown/ambiguous/non-exact match fail closed),
  - deployment-mode source enforcement (explicit CLI flag only; no implicit defaults/artifact-derived mode selection),
  - deployment-mode propagation enforcement for required subprocess delegations (explicit flag forwarding required; env override forbidden),
  - subprocess delegation classification enforcement (packaging-related `subprocess.*` invocations are in-scope; unrelated tools cannot affect mode selection),
  - static import-graph guard for harness-kernel `apps/api` isolation,
  - pre-package no-bypass validation gate checks under normal and exception-path flows,
  - artifact-parity determinism across integrated vs standalone outputs using frozen-profile canonical JSON bytes,
  - schema-typed artifact pre-parity validation enforcement,
  - mode-specific policy-override detection (forbidden in v47; fail closed),
  - policy-equivalence subject exact-match checks from frozen extraction sources only (`taskpack_verification_result@1`, `taskpack_closeout_evidence_bundle@1`),
  - policy-equivalence field-typing enforcement for set/boolean subjects under frozen canonical encodings,
  - deterministic packaging output-boundary checks (parity domain strictness vs manifest-described bundle domain),
  - deterministic packaging manifest ordering/hash stability across reruns,
  - deterministic emitted-file inventory normalization (`repo-relative posix`, dot-segment collapse) and `packaging_bundle_hash` stability across reruns,
  - packaging-bundle hash-subject completeness enforcement (normalized `path` + `sha256` per emitted-file record),
  - canonical-subject path-normalization enforcement for adapter-origin paths before hash/parity subject assembly,
  - deterministic rejection-diagnostic emission and ordering,
  - deterministic rejection-diagnostic `artifact_path` normalization before sort/emission,
  - deterministic rejection-diagnostic ordering tie-break enforcement (`policy_source` final tie-break),
  - diagnostics code-prefix/registry conformance (`AHK47` + authoritative registry),
  - required-error-channel enforcement (no warning downgrade),
  - stop-gate keyset continuity and deterministic cardinality assertions (`80`, computed from `metrics` keys only),
  - continuity-preservation assertions for v36-v46 frozen suites.
- Preserve deterministic environment posture for guard commands:
  - command examples run under `TZ=UTC`, `LC_ALL=C`, and `PYTHONHASHSEED=0` where relevant.

### Locks

- No-new-metric-keys lock is frozen:
  - v47 tests/guards may not introduce new stop-gate metric keys.
- Required-deterministic-env lock is frozen:
  - v47 guards fail closed if deterministic env contract drifts from `TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`.
- Required-mode-selection lock is frozen:
  - v47 guards fail closed on unknown mode selection, ambiguous mode resolution, or non-exact mode matching behavior.
- Required-mode-source lock is frozen:
  - v47 guards fail closed if deployment mode is not sourced from explicit CLI flag input,
  - v47 guards fail closed on implicit-default or artifact-derived mode selection.
- Required-mode-propagation lock is frozen:
  - v47 guards fail closed if required subprocess delegations omit explicit deployment-mode flag forwarding,
  - v47 guards fail closed on env-override-based mode propagation attempts.
- Required-subprocess-delegation-classification lock is frozen:
  - v47 guards fail closed if packaging-related subprocess delegations are not classified as in-scope mode-propagation checks.
- Required-validation-no-bypass lock is frozen:
  - v47 guards fail closed if packaging emit can occur after validation failure.
- Required-artifact-parity lock is frozen:
  - v47 guards fail closed if canonical artifact parity subjects differ across modes,
  - v47 guards fail closed if schema-typed artifacts fail pre-parity validation.
- Required-policy-equivalence lock is frozen:
  - v47 guards fail closed if frozen policy-equivalence subjects drift across modes.
- Required-policy-equivalence-field-typing lock is frozen:
  - v47 guards fail closed if frozen policy-equivalence field typing/encoding rules drift.
- Required-policy-equivalence-source lock is frozen:
  - v47 guards fail closed if policy-equivalence extraction source drifts from frozen authoritative artifacts.
- Required-mode-policy-override lock is frozen:
  - v47 guards fail closed if mode adapters attempt policy-semantic override.
- Required-packaging-manifest-bundle-authority lock is frozen:
  - v47 guards fail closed if emitted-file inventory normalization or `packaging_bundle_hash` determinism drifts,
  - v47 guards fail closed if bundle-hash subject omits normalized `path` or `sha256` record fields.
- Required-rejection-diagnostics lock is frozen:
  - v47 guards fail closed if packaging failures do not produce deterministic structured diagnostics,
  - v47 guards fail closed if deterministic ordering tie-break on `policy_source` drifts.
- Required-diagnostic-path-normalization lock is frozen:
  - v47 guards fail closed if diagnostic `artifact_path` normalization drifts from repo-relative posix dot-segment-collapsed form.
- Required-canonical-subject-path-normalization lock is frozen:
  - v47 guards fail closed if adapter-origin canonical-subject path normalization drifts.
- Required-provenance-hash-subject lock is frozen:
  - v47 guards fail closed if deterministic packaging provenance hash subject includes non-deterministic fields.
- Required-severity-policy lock is frozen:
  - v47 guards fail closed if required violations are emitted as warnings.
- Continuity-preservation lock is frozen:
  - v47 guards fail closed if v36-v46 continuity suites regress.

### Acceptance

- Guard suites pass deterministically across reruns.
- Required packaging wiring, parity, and fail-closed assertions are green.
- v36-v46 continuity guard suites remain green under v47 scope.

## Stop-Gate Impact (v47)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80` fail closed.
- v47 closeout must include runtime-observability comparison row against v46 baseline.
- v47 closeout must include packaging wiring evidence block:
  - block schema is docs-only `v33d_packaging_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `integrated_entrypoint`
    - `standalone_entrypoint`
    - `deployment_modes`
    - `artifact_parity_passed`
    - `policy_equivalence_passed`
    - `provenance_hash`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v46`
    - `notes`

## Error/Exit Policy (v47)

- No new URM error-code family is introduced in this arc.
- Harness diagnostics namespace (`AHK[0-9]{4}`) in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- v47 packaging diagnostics are constrained to `AHK47xx`, which is an arc-scoped subset of `AHK[0-9]{4}`, and must resolve through an authoritative registry.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V33-D deterministic integrated+standalone packaging lane MVP`
2. `tests: add v47 packaging determinism, policy-equivalence, and fail-closed guard suite`

## Intermediate Preconditions (for v47 start)

1. v46 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v46 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md`
3. Existing v46 verifier/evidence entrypoints remain available at v47 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
4. Existing v46 closeout artifacts remain available at v47 start:
   - `artifacts/quality_dashboard_v46_closeout.json`
   - `artifacts/stop_gate/metrics_v46_closeout.json`
   - `artifacts/stop_gate/report_v46_closeout.md`
   - `artifacts/agent_harness/v46/taskpack_profile_registry.json`
   - `artifacts/agent_harness/v46/profiles/v46_closeout_profile.json`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v46 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `W1` and `W2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic integrated+standalone packaging MVP (`V33-D`) is closed and test-covered.
- v47 closeout evidence includes runtime-observability comparison row against v46 baseline and `v33d_packaging_wiring_evidence@1` block.
- v36-v46 continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
