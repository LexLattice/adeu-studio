# Assessment vNext+53 Edges (Pre-Lock)

This document records pre-lock edge planning for `vNext+53` (`V34-E`
remote/enclave-attested verifier ingestion baseline).

Status: pre-lock assessment (March 7, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS53_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": true,
  "authoritative_scope": "v53_prelock_edge_planning",
  "required_in_decision": true,
  "notes": "This document is authoritative for v53 pre-lock edge planning until superseded by post-closeout disposition."
}
```

## Scope

- In scope: thin `V34-E` baseline over provider-neutral attestation normalization,
  deterministic attestation validation, exact local-equivalence guards, and closeout
  evidence integration.
- Out of scope: live provider adapters, network transport or remote job dispatch,
  deployment-mode expansion, broader policy recomputation, `V34-F`, `V34-G`,
  stop-gate schema-family fork, metric-key expansion, and generalized `L2` release.

## Inputs

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/write_closeout_evidence.py`
- `packages/adeu_agent_harness/src/adeu_agent_harness/matrix_parity.py`
- `packages/adeu_agent_harness/tests/test_taskpack_verifier.py`
- `packages/adeu_agent_harness/tests/test_taskpack_signature.py`
- `artifacts/quality_dashboard_v52_closeout.json`
- `artifacts/stop_gate/metrics_v52_closeout.json`
- `artifacts/agent_harness/v52/evidence_inputs/runtime_observability_comparison_v52.json`
- `artifacts/agent_harness/v52/evidence_inputs/metric_key_continuity_assertion_v52.json`
- `artifacts/agent_harness/v52/evidence_inputs/v34c_policy_recompute_evidence_v52.json`
- `artifacts/agent_harness/v52/evidence_inputs/v34d_retry_context_evidence_v52.json`
- `artifacts/agent_harness/v52/verification/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.json`

## Current Repo Reality

1. Local verifier execution is real and deterministic on `main`.
   - `verify_taskpack_run.py` emits `taskpack_verification_result@1` over current local
     authoritative inputs.
2. V34-A signing and trust-anchor registry reuse are real and deterministic on `main`.
   - `verify_taskpack_signature.py` already validates trust-anchor registry bindings and
     emits deterministic `signature_verification_result@1`.
3. No released `remote_enclave_attestation@1` artifact exists on `main`.
4. No released `attestation_verification_result@1` artifact exists on `main`.
5. No shared provider-neutral attestation normalizer/validator exists on `main`.
6. No verifier path currently accepts externally supplied attested verifier outputs on
   `main`.
7. Deployment mode remains frozen to `adeu_integrated` / `standalone` and singleton runtime
   `local_python_cli`; `remote_enclave` is not a released runtime or packaging mode.

## Pre-Lock Edge Set (Draft)

1. Provider-specific attestation format drift risk: `open`.
   - no provider-neutral attestation schema exists on `main`; accepting provider-native
     evidence directly would make authority shape caller-dependent.
2. Parallel trust-anchor system risk: `open`.
   - V34-A already established a trust-anchor registry contract; a second attestation-only
     registry would fragment authority unless explicitly forbidden.
3. External attested-result without local-equivalence risk: `open`.
   - no current path proves that an externally supplied attested verifier result exactly
     matches the current local verifier output for identical inputs.
4. Remote transport/job dispatch overreach risk: `open`.
   - `V34-E` can easily widen into remote execution orchestration unless the first slice is
     held to ingestion/validation only.
5. Deployment-mode creep risk: `open`.
   - `remote_enclave` deployment mode is a separate deferred path and should not bleed into
     the first attestation baseline.
6. Provider-id surface ambiguity risk: `open`.
   - no closed provider-id enum exists on `main`; leaving it open would create false
     generality and unstable fixtures.
7. Reference-time wall-clock drift risk: `open`.
   - attestation validation needs explicit reference time and must not default to wall clock
     or environment-derived time.
8. Non-normalized provider-evidence authority risk: `open`.
   - raw provider claims or transport wrappers are not currently fenced from becoming
     authority input.
9. Attested/local verified-result hash mismatch acceptance risk: `open`.
   - externally supplied verified results could be accepted without current local verifier
     equivalence unless the path is explicitly fail-closed.
10. Closeout evidence integration gap: `open`.
   - current closeout surfaces contain no canonical v34e attestation evidence slot.
11. Stop-gate churn risk: `open`.
   - the attestation lane should not widen stop-gate schema family or metric cardinality.
12. Nondeterministic environment-field leakage risk: `open`.
   - provider evidence often carries wall-clock, host, endpoint, or nonce fields that would
     destabilize replay if not frozen as non-authoritative.
13. Attested verified-result schema divergence risk: `open`.
   - the safest thin baseline should reuse the current `taskpack_verification_result@1`
     contract rather than define a parallel remote-only verifier output family.
14. Over-broad `L2` release interpretation risk: `open`.
   - `V34-E` is an `L2-candidate`, but the first slice should authorize only the attested
     ingestion lane, not generalized remote execution authority.
15. `attestation_verified` truth-value ambiguity risk: `open`.
   - a first attestation slice must require `attestation_verified == true`; field presence
     alone is not enough for acceptance.
16. Stale local-equivalence baseline reuse risk: `open`.
   - local equivalence must compare against a local verifier result materialized in the
     current v53 flow rather than whatever prior verification artifact happens to exist.
17. Shared verification-result schema authority ambiguity risk: `open`.
   - `taskpack_verification_result@1` should remain a shared schema contract for both local
     and attested outputs, while authority comes from explicit hashed artifacts, not a
     generic verifier artifact reference.
18. Malformed-but-hashable attested result acceptance risk: `open`.
   - the attested verifier output must validate against `taskpack_verification_result@1`
     before its hash participates in local-equivalence evaluation.
19. Raw provider-evidence hash subject creep risk: `open`.
   - `opaque_provider_evidence_hash` should bind normalized attestation to raw provider
     bytes for audit only and must not become part of the exact local-equivalence subject.
20. Duplicate/conflicting normalized-claim resolution drift risk: `open`.
   - normalization must fail closed on duplicate or conflicting normalized claims rather
     than silently choose one representation.
21. Artifact-ingestion-only rule ambiguity risk: `open`.
   - forbidding network transport is not sufficient unless the positive rule is also frozen:
     v53 attestation inputs must come from explicit local artifact paths only.
22. `runner_provenance_hash` subject ambiguity risk: `open`.
   - v53 uses `runner_provenance_hash` in normalized claims and binding checks, so the hash
     subject must be frozen to the full canonical `taskpack_runner_provenance@1` artifact.
23. Current local verifier materialization failure ambiguity risk: `open`.
   - if the current local verifier result cannot be materialized in the v53 flow, the arc
     must fail closed instead of silently weakening local equivalence.
24. Shared attestation-validator identifier comparability risk: `open`.
   - closeout evidence should require a frozen comparable identifier format rather than free
     text.
25. Provider-id comparison normalization risk: `open`.
   - the singleton provider check should be exact and case-sensitive rather than relying on
     helpful normalization.
26. Post-normalization duplicate/conflict timing ambiguity risk: `open`.
   - duplicate/conflicting claim rejection must happen after normalization into the
     provider-neutral schema, not before.
27. Equivalence-subject versus binding-envelope ambiguity risk: `open`.
   - the exact local-equivalence subject should stay limited to `verified_result_hash`,
     while the binding fields separately guard input identity.

## Recommended Thin Slice

1. Treat `v53` as an attested verifier-ingestion baseline only.
   - shared provider-neutral attestation normalizer/validator
   - deterministic `remote_enclave_attestation@1`
   - deterministic `attestation_verification_result@1`
2. Freeze authority to current local verifier outputs plus existing V34-A trust-anchor
   registry.
   - reuse `taskpack_verification_result@1`
   - reuse `taskpack_trust_anchor_registry@1`
   - no parallel attestation registry in v53
3. Keep provider scope intentionally tiny.
   - singleton `provider_id` only
   - no live provider adapters or network transport in v53
4. Make exact local-equivalence required and test-backed.
   - attested verified result hash must equal current local verified result hash for
     identical authoritative inputs
5. Add canonical closeout evidence and guard suites in the same arc.
   - the lane is not real until closeout can prove the normalized attestation, validation
     result, and exact local-equivalence posture on `main`
6. Freeze attestation truth, schema validation, and current-flow equivalence posture before
   implementation starts.
   - `attestation_verified == true` required
   - attested result must validate against `taskpack_verification_result@1` before hashing
   - local verifier result must be recomputed in the current v53 flow
7. Freeze artifact-ingestion-only and normalized-claim conflict posture before implementation
   starts.
   - explicit local artifact paths only
   - duplicate/conflicting normalized claims fail closed
   - `opaque_provider_evidence_hash` remains audit-only and non-equivalence-bearing
8. Freeze hash-subject and equivalence-envelope semantics before implementation starts.
   - `runner_provenance_hash` means the full canonical `taskpack_runner_provenance@1`
     artifact hash
   - current local verifier materialization failure fails closed
   - exact equivalence subject remains `verified_result_hash` only
9. Freeze singleton identifier semantics before implementation starts.
   - `provider_id` comparison is exact and case-sensitive
   - `shared_attestation_validator_identifier` must be a frozen comparable module/function
     path or registry key, not free text

## Pre-Lock Summary (Machine-Checkable)

```json
{
  "schema": "v53_prelock_edge_summary@1",
  "arc": "vNext+53",
  "target_path": "V34-E",
  "identified_edge_count": 27,
  "recommended_scope": "thin_v34e_attested_ingestion_baseline_only",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "blocking_themes": [
    "provider_neutral_normalization_must_be_frozen",
    "runner_provenance_hash_subject_must_be_frozen",
    "trust_anchor_reuse_must_remain_single_source",
    "provider_scope_must_stay_singleton_for_v53",
    "provider_id_comparison_must_be_exact_case_sensitive",
    "attestation_verified_must_equal_true",
    "attested_result_schema_validation_must_precede_hash_equivalence",
    "exact_local_equivalence_must_be_required",
    "current_local_equivalence_baseline_must_be_recomputed_in_flow",
    "local_materialization_failure_must_fail_closed",
    "shared_attestation_validator_identifier_must_be_comparable",
    "artifact_ingestion_only_rule_must_be_explicit",
    "opaque_provider_evidence_hash_must_remain_audit_only",
    "normalized_claim_conflicts_must_fail_closed",
    "equivalence_subject_and_binding_envelope_must_remain_distinct",
    "remote_transport_and_job_dispatch_must_be_forbidden",
    "deployment_mode_expansion_must_remain_deferred",
    "attestation_reference_time_must_be_explicit",
    "closeout_evidence_slot_must_be_added"
  ]
}
```

## Recommendation

1. Draft `v53` as a thin `V34-E` baseline over attested verifier-output ingestion only.
2. Keep live provider adapters, remote execution transport, and `remote_enclave`
   deployment-mode release deferred.
3. Require exact local-equivalence against the current local verifier output before treating
   attested output as acceptable in this arc.
4. Require deterministic attestation, validation-result, and canonical `v34e` evidence
   artifacts before treating the lane as closed.
