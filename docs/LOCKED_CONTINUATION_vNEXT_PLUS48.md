# Locked Continuation vNext+48 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 5, 2026 UTC).

Decision basis:

- `vNext+47` (`V33-D`, `W1`/`W2`) is merged on `main` via PR `#243` and PR `#244` with green CI checks.
- `vNext+47` closeout decision capture is recorded in `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md` with `all_passed = true`.
- Post-v47 planning baseline is `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`.
- Selected v48 thin-slice default is signing/trust-anchor pre-flight hardening:
  - `V34-A` (taskpack signing + trust-anchor distribution).
- `vNext+48` is constrained to deterministic additive hardening for `V34-A` only:
  - no matrix-lane parity release (`V34-B`) in this arc,
  - no zero-trust recompute release (`V34-C`) in this arc,
  - no retry-context feeder release (`V34-D`) in this arc,
  - no enclave attestation release (`V34-E`) in this arc,
  - no standalone integrity verifier release (`V34-F`) in this arc,
  - no deployment-mode expansion release (`V34-G`) in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v48,
  - v48 keyset must be exactly equal to v47 keyset (set equality, derived cardinality),
  - baseline derived cardinality at v48 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- v36-v47 continuity guarantees remain frozen as release preconditions:
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
  - verifier/evidence-writer continuity remains authoritative,
  - packaging continuity remains authoritative.
- Boundary-release scope lock for v48 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- Authority model lock is frozen:
  - signature verification authority derives from canonical artifacts (`taskpack_manifest`, bundle hash subject, signature envelope, trust-anchor registry),
  - free-form repository prose and model natural-language self-claims are non-authoritative for policy decisions.
- Signature subject lock is frozen:
  - signing subject is `taskpack_bundle_hash` only,
  - `taskpack_manifest_hash` is required as bound redundant field.
- Envelope scope lock is frozen:
  - `V34-A` supports single-signature envelope semantics only,
  - multi-signer quorum or merge-policy governance is not authorized in this arc.
- Verification topology lock is frozen:
  - signature verification must run as deterministic pre-flight,
  - downstream runner/verifier/packaging lanes consume `signature_verification_result@1` rather than redefining verification policy independently.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `X1` Deterministic signing envelope + trust-anchor registry + pre-flight verification artifact MVP (`V34-A`)
2. `X2` Signing determinism/downgrade-protection/fail-closed guard suite (`V34-A`)

Out-of-scope note:

- matrix-lane parity (`V34-B`) in this arc,
- independent policy recomputation (`V34-C`) in this arc,
- retry-context feeder automation (`V34-D`) in this arc,
- remote/enclave attested verifier execution (`V34-E`) in this arc,
- standalone integrity self-verification (`V34-F`) in this arc,
- `remote_enclave` deployment mode expansion (`V34-G`) in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v48)

- v49+ adapter matrix-lane parity checks (`V34-B`) under explicit lock text.
- v50+ independent zero-trust policy-validation recomputation (`V34-C`) under explicit lock text.
- v51+ rejection-diagnostic retry-context feeder automation (`V34-D`) under explicit lock text.
- v52+ remote/enclave attested verifier execution (`V34-E`) under explicit `L2` lock text.
- v53+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock text.
- v54+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.

## V47 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md",
  "target": "V34-A",
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
    "V33_C_VERIFIER_CONTINUITY_GREEN",
    "V33_D_PACKAGING_CONTINUITY_GREEN"
  ],
  "expected_relation": "all_required_continuity_guards_remain_green"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v48.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-A Signing Contract Assertion (Machine-Checkable)

```json
{
  "schema": "v34a_signing_contract@1",
  "target_arc": "vNext+48",
  "target_path": "V34-A",
  "signing_authority_inputs": {
    "taskpack_manifest": "required",
    "taskpack_bundle_hash": "required_manifest_authority_subject",
    "taskpack_manifest_hash": "required_redundant_binding",
    "signature_envelope_schema": "taskpack_signature_envelope@1",
    "signature_envelope_required": true,
    "trust_anchor_registry_schema": "taskpack_trust_anchor_registry@1",
    "trust_anchor_registry_required": true,
    "verification_reference_time_utc": "required_explicit_input_no_wall_clock_default"
  },
  "signing_execution_interface": {
    "kernel_package_authority": "packages/adeu_agent_harness",
    "preflight_entrypoint": "python -m adeu_agent_harness.verify_taskpack_signature",
    "signature_verification_result_schema": "signature_verification_result@1",
    "signature_verification_result_authority_fields": [
      "taskpack_manifest_hash",
      "taskpack_bundle_hash",
      "signature_envelope_hash",
      "trust_anchor_registry_hash",
      "verification_reference_time_utc",
      "preflight_invocation_binding_hash",
      "signer_key_id",
      "algorithm",
      "verified"
    ],
    "verification_phase": "pre_runner_verifier_packaging_required",
    "downstream_consumption_policy": "consume_signature_verification_result@1_with_verified_true_required",
    "downstream_binding_check_policy": "required_exact_hash_binding_check_before_execution",
    "downstream_required_binding_checks": [
      "taskpack_manifest_hash",
      "taskpack_bundle_hash",
      "signature_envelope_hash",
      "trust_anchor_registry_hash",
      "verification_reference_time_utc",
      "preflight_invocation_binding_hash",
      "signer_key_id",
      "algorithm",
      "verified"
    ],
    "preflight_handoff_policy": "in_process_orchestrated_handoff_required_no_user_supplied_signature_verification_result_path",
    "input_mode": "artifact_only_non_interactive",
    "single_signature_only": true,
    "algorithm_policy_enum": [
      "ed25519",
      "p256"
    ],
    "algorithm_profile": {
      "ed25519": {
        "public_key_format": "raw_32b_base64",
        "signature_format": "raw_64b_base64"
      },
      "p256": {
        "curve": "secp256r1",
        "public_key_format": "spki_der_base64",
        "signature_format": "der_ecdsa"
      }
    },
    "algorithm_key_binding_policy": "required_exact_algorithm_match_between_envelope_and_registry_key_record",
    "preflight_invocation_binding_hash_definition": "sha256_canonical_json(preflight_entrypoint,taskpack_manifest_hash,taskpack_bundle_hash,signature_envelope_hash,trust_anchor_registry_hash,verification_reference_time_utc)",
    "signature_subject": "taskpack_bundle_hash",
    "redundant_bound_fields": [
      "taskpack_manifest_hash"
    ]
  },
  "signing_policy": {
    "authoritative_instruction_source": "canonical_artifacts_only",
    "trust_anchor_registry_single_source_required": true,
    "trust_anchor_registry_key_id_uniqueness_required": true,
    "trust_anchor_registry_required_key_fields": [
      "key_id",
      "algorithm",
      "public_key",
      "revoked",
      "expires_at_utc"
    ],
    "trust_anchor_key_lifecycle_policy": {
      "revoked_field_type": "boolean_required",
      "expires_at_utc_format": "rfc3339_utc_z_required_second_precision",
      "revoked_key_outcome": "fail_closed",
      "expired_key_outcome": "fail_closed",
      "expiry_evaluation_time_source": "verification_reference_time_utc_explicit_input_only",
      "wall_clock_time_as_expiry_source": "forbidden_non_v48"
    },
    "signer_key_selection_policy": "exactly_one_key_id_match_required_else_fail_closed",
    "crypto_library_selection_policy": "verification_library_must_be_explicitly_declared_and_dependency_pinned_no_dynamic_provider_fallback",
    "multi_signer_quorum_policy": "forbidden_non_v48",
    "verification_bypass": "forbidden_non_v48",
    "signature_verification_result_source_policy": "must_be_emitted_by_current_preflight_invocation",
    "user_supplied_signature_verification_result_artifact": "forbidden_non_v48",
    "verification_failure_outcome": "fail_closed_no_downstream_execution",
    "deterministic_signature_verification_result_required": true,
    "signature_verification_result_nondeterministic_fields_forbidden": [
      "wall_clock_timestamp",
      "host_identity",
      "absolute_paths",
      "random_nonce"
    ]
  },
  "diagnostics_policy": {
    "schema": "v34a_signing_rejection_diagnostic@1",
    "issue_code_parent_namespace": "AHK[0-9]{4}",
    "issue_code_prefix": "AHK48",
    "issue_code_format": "AHK48[0-9]{2}",
    "registry_authority_path": "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v48.json",
    "required_on_verification_failure": true,
    "required_violation_channel": "error_only_non_zero_exit"
  },
  "stop_gate_continuity_policy": {
    "schema_family": "stop_gate_metrics@1",
    "baseline_metrics_artifact": "artifacts/stop_gate/metrics_v47_closeout.json",
    "metric_key_change": "forbidden",
    "expected_keyset_relation": "exact_set_equality_with_v47",
    "expected_cardinality": 80,
    "cardinality_authority": "metrics_object_keys_only",
    "cardinality_check": "computed_metric_key_cardinality_equals_expected_cardinality_fail_closed"
  },
  "closeout_doc_policy": {
    "decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md",
    "required_json_blocks": [
      "runtime_observability_comparison@1",
      "metric_key_continuity_assertion@1",
      "v34a_signing_wiring_evidence@1"
    ]
  },
  "fail_closed_conditions": [
    "signature_envelope_missing_or_malformed",
    "trust_anchor_registry_missing_or_malformed",
    "multiple_signatures_detected",
    "signature_subject_mismatch_detected",
    "taskpack_manifest_hash_binding_missing_or_mismatch",
    "signer_key_id_not_found",
    "signer_key_id_non_unique_in_registry",
    "signer_key_selection_ambiguous",
    "algorithm_key_binding_mismatch_detected",
    "signature_cryptographic_verification_failed",
    "preflight_verification_bypass_detected",
    "signature_verification_result_missing_or_malformed",
    "signature_verification_result_input_hash_binding_mismatch",
    "signature_verification_result_source_untrusted_or_unbound",
    "user_supplied_signature_verification_result_path_detected",
    "signature_verification_result_verified_false_for_downstream_execution",
    "signature_verification_result_contains_nondeterministic_fields",
    "verification_reference_time_missing_or_malformed",
    "verification_reference_time_wall_clock_default_detected",
    "trust_anchor_key_revoked_field_type_invalid",
    "trust_anchor_key_expires_at_utc_format_invalid",
    "trust_anchor_key_marked_revoked",
    "trust_anchor_key_expired_for_verification_reference_time",
    "required_contract_violation_reported_as_warning",
    "stop_gate_metric_keyset_drift",
    "stop_gate_metric_cardinality_authority_drift"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## X1) Deterministic Signing + Trust-Anchor Pre-Flight MVP (`V34-A`)

### Goal

Introduce deterministic pre-flight signature verification over canonical taskpack authority artifacts.

### Scope

- add signature envelope schema (`taskpack_signature_envelope@1`), single-signature semantics only;
- add trust-anchor registry schema (`taskpack_trust_anchor_registry@1`) with key-id to algorithm pinning and lifecycle fields (`revoked`, `expires_at_utc`);
- add pre-flight verification entrypoint to validate subject/hash bindings and signature correctness;
- require explicit `verification_reference_time_utc` input for key-expiry evaluation (no wall-clock default);
- freeze invocation binding hash subject as `sha256_canonical_json(preflight_entrypoint, taskpack_manifest_hash, taskpack_bundle_hash, signature_envelope_hash, trust_anchor_registry_hash, verification_reference_time_utc)`;
- emit deterministic `signature_verification_result@1` for downstream consumption;
- bind `signature_verification_result@1` to the current pre-flight invocation via deterministic invocation binding hash;
- fail closed on missing/invalid/ambiguous signing inputs.

### Locks

- single-signature envelope only in v48;
- signature subject is `taskpack_bundle_hash` only;
- algorithm/key downgrade attempts fail closed;
- signer key selection requires exactly one `signer_key_id` match in registry; zero or multi-match fails closed;
- trust-anchor lifecycle field types are frozen (`revoked` boolean required; `expires_at_utc` RFC3339 UTC `Z` second-precision required);
- revoked or expired signer keys fail closed using explicit `verification_reference_time_utc` evaluation;
- downstream lanes may proceed only when `signature_verification_result@1.verified == true`;
- downstream lanes must perform exact binding checks on `taskpack_manifest_hash`, `taskpack_bundle_hash`, `signature_envelope_hash`, `trust_anchor_registry_hash`, `verification_reference_time_utc`, `preflight_invocation_binding_hash`, `signer_key_id`, `algorithm`, and `verified` before execution;
- downstream lanes must reject user-supplied or unbound `signature_verification_result@1` artifacts that were not emitted by the current pre-flight invocation;
- cryptographic verification library must be explicitly declared and dependency-pinned; dynamic provider fallback is forbidden;
- downstream execution without valid pre-flight verification is forbidden.

### Acceptance

- identical signing inputs produce byte-identical verification result artifacts;
- invalid/malformed signatures fail closed with deterministic diagnostics;
- pre-flight verification artifact is required and consumed by downstream lanes.

## X2) Signing Determinism + Fail-Closed Guard Suite (`V34-A`)

### Goal

Prove deterministic signature verification behavior and downgrade-protection posture for v48.

### Scope

- add deterministic tests/guards for:
  - envelope schema validation,
  - trust-anchor registry schema validation,
  - single-signature-only enforcement,
  - signature subject and redundant binding validation,
  - algorithm/key pinning enforcement,
  - invocation-binding hash subject-definition enforcement,
  - signer key lifecycle checks (`revoked`, `expires_at_utc`) with explicit verification-time evaluation,
  - trust-anchor lifecycle field-type/format enforcement (`revoked` boolean, `expires_at_utc` RFC3339 UTC `Z`),
  - pre-flight verification no-bypass control flow,
  - pre-flight artifact source-binding enforcement (reject spoofed/user-supplied verification artifacts),
  - deterministic diagnostics emission and ordering,
  - required error-channel enforcement,
  - stop-gate keyset/cardinality continuity assertions (`80`, keys only authority),
  - continuity-preservation assertions for v36-v47 frozen suites.
- preserve deterministic environment posture for guard commands:
  - `TZ=UTC`, `LC_ALL=C`, `PYTHONHASHSEED=0`.

### Locks

- no-new-metric-keys lock is frozen;
- required-deterministic-env lock is frozen;
- required-single-signature lock is frozen;
- required-preflight-no-bypass lock is frozen;
- required-algorithm-key-pinning lock is frozen;
- required-severity-policy lock is frozen;
- continuity-preservation lock is frozen.

### Acceptance

- guard suites pass deterministically across reruns;
- required signing wiring and fail-closed assertions are green;
- v36-v47 continuity guard suites remain green under v48 scope.

## Stop-Gate Impact (v48)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80` fail closed.
- v48 closeout must include runtime-observability comparison row against v47 baseline.
- v48 closeout must include signing wiring evidence block:
  - block schema is docs-only `v34a_signing_wiring_evidence@1`,
  - required keys are:
    - `schema`
    - `preflight_entrypoint`
    - `signature_subject`
    - `single_signature_only`
    - `algorithm_key_binding_enforced`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v47`
    - `notes`

## Error/Exit Policy (v48)

- No new URM runtime error-code family is introduced in this arc.
- Harness diagnostics namespace (`AHK[0-9]{4}`) in this arc is contract-diagnostics authority only and is not a URM runtime error-code family.
- v48 signing diagnostics are constrained to `AHK48xx`, which is an arc-scoped subset of `AHK[0-9]{4}`, and must resolve through an authoritative registry.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add V34-A signing envelope + trust-anchor registry MVP`
2. `tests: add v48 signing determinism and fail-closed guard suite`

## Intermediate Preconditions (for v48 start)

1. v47 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v47 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS47.md`
3. Existing v47 packaging entrypoints remain available at v48 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux_integrated.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux_standalone.py`
4. Existing v47 closeout artifacts remain available at v48 start:
   - `artifacts/quality_dashboard_v47_closeout.json`
   - `artifacts/stop_gate/metrics_v47_closeout.json`
   - `artifacts/stop_gate/report_v47_closeout.md`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v47 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `X1` and `X2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- Deterministic signing/trust-anchor pre-flight MVP (`V34-A`) is closed and test-covered.
- v48 closeout evidence includes runtime-observability comparison row against v47 baseline and `v34a_signing_wiring_evidence@1` block.
- v36-v47 continuity remains green and unreverted.
- No solver semantics contract delta and no trust-lane regression introduced.
