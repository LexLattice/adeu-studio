# Locked Continuation vNext+49 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`
- `docs/ASSESSMENT_vNEXT_PLUS48_PRE_V49_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 6, 2026 UTC).

## Decision Basis

- `vNext+48` (`V34-A`, `X1`/`X2`) is merged on `main` via PR `#245` and PR `#246`.
- `vNext+48` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md` with `all_passed = true`.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` defaulted `vNext+49` to `V34-B`.
- `docs/ASSESSMENT_vNEXT_PLUS48_PRE_V49_EDGES.md` found that `V34-A` is closed at the
  contract/verifier/helper level but not yet fully closed at the harness-pipeline level.
- `vNext+49` therefore overrides the default `V34-B` sequencing and is constrained to one
  thin `V34-A` completion slice only:
  - downstream handoff enforcement;
  - canonical signing evidence integration;
  - continuity-guard repair.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v49,
  - v49 keyset must be exactly equal to v48 keyset,
  - baseline derived cardinality at v49 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v49 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- `V34-A` signing contract continuity remains frozen:
  - signing subject remains `taskpack_bundle_hash`,
  - `taskpack_manifest_hash` remains the required redundant bound field,
  - single-signature envelope posture remains frozen,
  - algorithm enum and key-binding policy remain unchanged,
  - trust-anchor lifecycle evaluation remains bound to explicit
    `verification_reference_time_utc`.
- Verification-topology completion lock for v49 is frozen:
  - v48 semantics are not being redefined,
  - v49 must complete the already-declared downstream handoff and evidence integration
    rather than introducing an alternate signing policy.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `X3` Orchestrated downstream signature-result handoff enforcement (`V34-A` completion)
2. `X4` Canonical signing evidence integration + continuity-guard repair (`V34-A` completion)

Out-of-scope note:

- matrix-lane parity (`V34-B`) in this arc,
- independent policy recomputation (`V34-C`) in this arc,
- retry-context feeder automation (`V34-D`) in this arc,
- remote/enclave attested verifier execution (`V34-E`) in this arc,
- standalone integrity self-verification (`V34-F`) in this arc,
- `remote_enclave` deployment mode expansion (`V34-G`) in this arc,
- multi-signer/quorum policy in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v49)

- v50+ adapter matrix-lane parity checks (`V34-B`) only after `V34-A` handoff completion is
  closed on `main`.
- v51+ independent zero-trust policy-validation recomputation (`V34-C`) under explicit lock
  text.
- v52+ rejection-diagnostic retry-context feeder automation (`V34-D`) under explicit lock
  text.
- v53+ remote/enclave attested verifier execution (`V34-E`) under explicit `L2` lock text.
- v54+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock
  text.
- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.

## V48 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md",
  "target": "V34-A-completion",
  "required_continuity_guards": [
    "V34_A_X1_SIGNING_MVP_GREEN",
    "V34_A_X2_SIGNING_GUARDS_GREEN"
  ],
  "expected_relation": "v48_contract_remains_frozen_while_downstream_handoff_and_evidence_integration_are_completed"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v49.
- this narrowed machine-checkable consumption block is v48-local only and does not weaken the
  global continuity locks declared above; v36-v48 baseline continuity remains in force for the
  arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-A Handoff Completion Contract (Machine-Checkable)

```json
{
  "schema": "v34a_handoff_completion_contract@1",
  "target_arc": "vNext+49",
  "target_path": "V34-A",
  "preserved_authority_inputs": {
    "taskpack_manifest": "required",
    "taskpack_bundle_hash": "required_manifest_authority_subject",
    "taskpack_manifest_hash": "required_redundant_binding",
    "signature_envelope_schema": "taskpack_signature_envelope@1",
    "trust_anchor_registry_schema": "taskpack_trust_anchor_registry@1",
    "signature_verification_result_schema": "signature_verification_result@1",
    "verification_reference_time_utc": "required_explicit_input_no_wall_clock_default"
  },
  "downstream_handoff_requirements": {
    "shared_binding_validator": "packages/adeu_agent_harness.verify_taskpack_signature.validate_signature_verification_result_for_downstream",
    "runner_consumption_required": true,
    "verifier_consumption_required": true,
    "packaging_consumption_required": true,
    "closeout_evidence_integration_required": true,
    "verified_must_equal_true": true,
    "accepted_handoff_mode": "must_be_emitted_by_current_preflight_entrypoint_and_match_frozen_preflight_invocation_binding_hash",
    "stale_handoff_artifact_definition": "any_signature_verification_result_whose_required_binding_fields_do_not_exactly_match_current_authoritative_inputs",
    "detached_or_stale_handoff_artifact": "forbidden_fail_closed",
    "authoritative_packaging_gate_for_v49": "packaging_entrypoints_must_reject_missing_stale_or_unbound_signature_handoff_before_packaging_manifest_emission",
    "same_snapshot_taskpack_binding_required": true,
    "runtime_taskpack_hash_recomputation_policy": "each_downstream_path_must_recompute_current_manifest_and_bundle_hashes_from_the_same_taskpack_bytes_it_then_consumes",
    "required_binding_checks": [
      "taskpack_manifest_hash",
      "taskpack_bundle_hash",
      "signature_envelope_hash",
      "trust_anchor_registry_hash",
      "verification_reference_time_utc",
      "preflight_invocation_binding_hash",
      "signer_key_id",
      "algorithm",
      "verified"
    ]
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34a_handoff_completion_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "preflight_entrypoint",
      "runner_entrypoint",
      "verifier_entrypoint",
      "evidence_writer_entrypoint",
      "packaging_entrypoints",
      "shared_binding_validator_used",
      "binding_fields_verified",
      "verified_required",
      "signature_result_consumed_by_runner",
      "signature_result_consumed_by_verifier",
      "signature_result_consumed_by_packaging",
      "current_taskpack_snapshot_binding_enforced",
      "detached_user_supplied_handoff_forbidden",
      "historical_v47_to_v48_continuity_guard_repaired",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v48",
      "notes"
    ],
    "sidecar_only_evidence_posture": "forbidden"
  },
  "test_repair_requirements": {
    "historical_guard_target": "packages/adeu_agent_harness/tests/test_taskpack_signature.py",
    "v47_to_v48_metric_keyset_guard_must_compare_distinct_artifacts": true,
    "historical_self_compare_configuration": "forbidden_fail_closed",
    "baseline_current_metric_artifact_paths_must_differ": true
  },
  "fail_closed_conditions": [
    "signature_verification_result_missing_for_downstream_runner",
    "signature_verification_result_missing_for_downstream_verifier",
    "signature_verification_result_missing_for_downstream_packaging",
    "signature_verification_result_binding_mismatch_accepted_by_downstream",
    "signature_verification_result_verified_false_accepted_by_downstream",
    "runtime_taskpack_snapshot_hash_mismatch_accepted_by_downstream",
    "stale_or_detached_signature_verification_result_accepted",
    "signing_handoff_evidence_missing_from_closeout",
    "historical_v47_to_v48_metric_keyset_guard_self_comparison_persists",
    "baseline_current_metric_artifact_self_compare_detected"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## X3) Orchestrated Downstream Signature-Result Handoff Enforcement (`V34-A`)

### Goal

Complete the v48 signing contract by enforcing signature-result handoff in the actual
downstream harness path.

### Scope

- wire the shared downstream signature-result validator into the runner path;
- wire the shared downstream signature-result validator into the verifier path;
- wire the shared downstream signature-result validator into the packaging path;
- require each downstream path to recompute the current `taskpack_manifest_hash` and
  `taskpack_bundle_hash` from the same taskpack bytes it then consumes for execution,
  verification, or packaging emission;
- require the active downstream path to reject missing, stale, detached, or unbound signing
  artifacts;
- keep the v48 signing authority model unchanged while making downstream consumption
  operationally real.

### Locks

- v49 must not redefine signature subject, algorithm policy, or trust-anchor registry policy;
- downstream enforcement must reuse the frozen v48 binding fields rather than introduce a
  parallel acceptance contract;
- presence of the `verified` field is insufficient; downstream must require
  `signature_verification_result@1.verified == true`;
- "stale" means any `signature_verification_result@1` whose required binding fields do not
  exactly match the current authoritative invocation inputs;
- downstream consumers must not hash one filesystem state and then execute, verify, or
  package a different taskpack state;
- recomputation must be over the exact bytes later consumed by the downstream path; hashing a
  cached, earlier, or later-reloaded taskpack snapshot and then consuming different bytes is
  forbidden;
- downstream must read taskpack bytes once, compute hashes from that buffer, and use that same
  buffer for execution, verification, or packaging emission;
- acceptance of detached or stale signing-result artifacts is forbidden;
- no downstream execution may proceed after a failed v34a handoff validation;
- packaging entrypoints are the authoritative packaging/evidence gate for this arc and must
  reject missing, stale, detached, or unbound signing-result handoff before packaging
  manifest emission;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- runner path fails closed when the required signing-result handoff is absent or unbound;
- verifier path fails closed when the required signing-result handoff is absent or unbound;
- packaging path fails closed when the required signing-result handoff is absent or unbound;
- the orchestrated downstream path only accepts signing results bound to the current
  pre-flight invocation;
- downstream paths fail closed if the current taskpack snapshot they consume recomputes a
  manifest or bundle hash different from the bound v48 signing result;
- identical inputs produce deterministic downstream handoff outcomes across reruns.

## X4) Canonical Signing Evidence Integration + Continuity-Guard Repair (`V34-A`)

### Goal

Close the remaining v48 evidence integration gap and repair the weak historical continuity
sentinel identified before v49 planning.

### Scope

- integrate signing-handoff completion evidence into the canonical closeout path;
- update the closeout/evidence or packaging surface so the signing lane is no longer only a
  docs-side sidecar claim;
- repair the v47-to-v48 metric-key continuity guard so it compares distinct authoritative
  artifacts;
- add deterministic tests/guards for the new downstream handoff and evidence requirements.

### Locks

- no stop-gate schema-family fork is authorized in this arc;
- no stop-gate metric-key expansion is authorized in this arc;
- evidence integration must remain additive over frozen v46/v47 evidence bundle behavior;
- closeout proof must distinguish between historical continuity evidence and the current
  v48-to-v49 stop-gate comparison;
- historical continuity repair must fail closed if
  `baseline_metrics_artifact == current_metrics_artifact`;
- historical continuity repair must fail closed if baseline and current artifact paths are
  identical, because that indicates self-comparison rather than continuity validation;
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v34a_handoff_completion_evidence@1` block;
- canonical downstream evidence no longer treats v48 signing wiring as sidecar-only;
- the repaired historical continuity guard fails if distinct v47/v48 keysets drift and does
  not compare a baseline artifact to itself;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v49)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v49 closeout must include runtime-observability comparison row against v48 baseline.
- v49 closeout must include metric-key continuity assertion against v48 baseline.
- v49 closeout must include handoff-completion evidence block:
  - block schema is docs-only `v34a_handoff_completion_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `preflight_entrypoint`
    - `runner_entrypoint`
    - `verifier_entrypoint`
    - `evidence_writer_entrypoint`
    - `packaging_entrypoints`
    - `shared_binding_validator_used`
    - `binding_fields_verified`
    - `verified_required`
    - `signature_result_consumed_by_runner`
    - `signature_result_consumed_by_verifier`
    - `signature_result_consumed_by_packaging`
    - `current_taskpack_snapshot_binding_enforced`
    - `detached_user_supplied_handoff_forbidden`
    - `historical_v47_to_v48_continuity_guard_repaired`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v48`
    - `notes`

## Error/Exit Policy (v49)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v49 introduces new handoff-specific harness diagnostics, they must be constrained to an
  authoritative `AHK49xx` registry and remain error-only with non-zero exit behavior.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: complete v34a downstream signing handoff in harness pipeline`
2. `tests: add v49 handoff/evidence guards and repair continuity sentinel`

## Intermediate Preconditions (for v49 start)

1. v48 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v48 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md`
3. Existing v48 signing verifier and helper remain available at v49 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
4. Existing v48 closeout artifacts remain available at v49 start:
   - `artifacts/quality_dashboard_v48_closeout.json`
   - `artifacts/stop_gate/metrics_v48_closeout.json`
   - `artifacts/stop_gate/report_v48_closeout.md`
   - `artifacts/agent_harness/v48/evidence_inputs/runtime_observability_comparison_v48.json`
   - `artifacts/agent_harness/v48/evidence_inputs/metric_key_continuity_assertion_v48.json`
   - `artifacts/agent_harness/v48/evidence_inputs/v34a_signing_wiring_evidence_v48.json`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v48 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `X3` and `X4` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-A` signing contract remains frozen and is now consumed in the downstream harness path.
- v49 closeout evidence includes runtime-observability comparison row against v48 baseline,
  metric-key continuity assertion against v48 baseline, and
  `v34a_handoff_completion_evidence@1`.
- the historical v47-to-v48 continuity sentinel is repaired and covered by deterministic
  tests.
- v36-v48 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
