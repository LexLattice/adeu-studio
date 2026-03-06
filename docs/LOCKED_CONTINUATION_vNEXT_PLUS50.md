# Locked Continuation vNext+50 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md`
- `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 6, 2026 UTC).

## Decision Basis

- `vNext+49` (`V34-A` completion, `X3`/`X4`) is merged on `main` with green CI checks.
- `vNext+49` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md` marks the `V34-A` downstream-handoff/evidence gap as
  closed and restores eligibility for explicit `V34-B` evaluation.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v8.md` still names `V34-B` as the next family candidate, but
  current harness reality is narrower than the full planning tuple:
  - `deployment_mode` is real and frozen to `adeu_integrated` / `standalone`,
  - `adapter_id` is real in runner provenance and adapter registry contracts,
  - `runtime_id` is not yet a released harness surface.
- `vNext+50` therefore selects one thin `V34-B` baseline slice only:
  - declared matrix-lane registry for currently released surfaces,
  - deterministic matrix-lane parity reporting over current deployment-mode and adapter lanes,
  - no multi-runtime or adapter-kind expansion in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v50,
  - v50 keyset must be exactly equal to v49 keyset,
  - baseline derived cardinality at v50 start is `80` and must remain unchanged in this arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v50 is frozen:
  - this arc authorizes no `L2` boundary release,
  - no additional governance or persistence authority release is authorized in this arc.
- `V34-A` signing and downstream-handoff completion remain frozen prerequisites:
  - signing subject remains `taskpack_bundle_hash`,
  - downstream runner/verifier/packaging consumption remains required and unchanged,
  - `v34a_handoff_completion_evidence@1` remains part of the canonical closeout surface.
- `V34-B` release-shape lock for v50 is frozen:
  - this arc is a matrix-baseline and reporting slice only,
  - `runtime_id` expansion beyond a singleton declared value is not authorized,
  - deployment mode expansion beyond `adeu_integrated` and `standalone` is not authorized,
  - adapter-kind expansion beyond `candidate_plan_passthrough` is not authorized,
  - matrix lanes must compose over existing runner/verifier/packaging contracts rather than
    redefine policy semantics.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `Y1` Declared matrix-lane registry + deterministic parity-report baseline (`V34-B`)
2. `Y2` Matrix-lane guard suite + current-lane parity enforcement (`V34-B`)

Out-of-scope note:

- independent zero-trust policy recomputation (`V34-C`) in this arc,
- rejection-diagnostic retry-context feeder automation (`V34-D`) in this arc,
- remote/enclave attested verifier execution (`V34-E`) in this arc,
- standalone integrity self-verification (`V34-F`) in this arc,
- `remote_enclave` deployment mode expansion (`V34-G`) in this arc,
- multi-runtime matrix expansion in this arc,
- adapter-kind expansion beyond current passthrough support in this arc,
- multi-signer/quorum policy in this arc,
- stop-gate metric-key expansion in this arc,
- stop-gate schema-family fork in this arc,
- runtime/provider/proposer endpoint expansion in this arc,
- solver/runtime semantics contract release in this arc.

## Deferred Follow-on Candidates (Non-v50)

- v51+ independent zero-trust policy-validation recomputation (`V34-C`) under explicit lock
  text.
- v52+ rejection-diagnostic retry-context feeder automation (`V34-D`) under explicit lock
  text.
- v53+ remote/enclave attested verifier execution (`V34-E`) under explicit `L2` lock text.
- v54+ standalone bundle integrity self-verification utility (`V34-F`) under explicit lock
  text.
- v55+ optional `remote_enclave` deployment mode (`V34-G`) under explicit lock text.
- future `V34-B` follow-on expansion only after v50 closure:
  - multi-runtime lane expansion,
  - adapter-kind expansion beyond `candidate_plan_passthrough`,
  - matrix parity beyond current released adapter/mode sets.

## V49 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md",
  "target": "V34-B-baseline",
  "required_continuity_guards": [
    "V34_A_X3_DOWNSTREAM_HANDOFF_GREEN",
    "V34_A_X4_CANONICAL_EVIDENCE_GREEN"
  ],
  "expected_relation": "v49_downstream_signing_and_closeout_contracts_remain_frozen_while_v34b_matrix_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v50.
- this narrowed machine-checkable consumption block is v49-local only and does not weaken the
  global continuity locks declared above; v36-v49 baseline continuity remains in force for the
  arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V34-B Matrix Baseline Contract (Machine-Checkable)

```json
{
  "schema": "v34b_matrix_baseline_contract@1",
  "target_arc": "vNext+50",
  "target_path": "V34-B",
  "preserved_authority_inputs": {
    "taskpack_manifest_hash": "required",
    "candidate_change_plan_hash": "required",
    "runner_provenance_schema": "taskpack_runner_provenance@1",
    "verified_result_schema": "taskpack_verification_result@1",
    "evidence_bundle_schema": "taskpack_closeout_evidence_bundle@1",
    "verifier_provenance_schema": "taskpack_verifier_provenance@1",
    "packaging_provenance_schema": "taskpack_packaging_provenance@1",
    "v34a_handoff_completion_contract": "required_frozen_precondition"
  },
  "matrix_lane_registry_requirements": {
    "registry_schema": "adapter_matrix@1",
    "parity_report_schema": "adapter_matrix_parity_report@1",
    "lane_id_tuple": [
      "deployment_mode",
      "adapter_id",
      "runtime_id"
    ],
    "declared_registry_only": true,
    "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
    "tuple_uniqueness_required": true,
    "tuple_order_policy": "lexicographic_over_deployment_mode_adapter_id_runtime_id",
    "deployment_mode_enum": [
      "adeu_integrated",
      "standalone"
    ],
    "adapter_id_source_policy": "must_reference_declared_runner_adapter_registry_ids_only",
    "adapter_kind_policy": "candidate_plan_passthrough_only_non_v50_expansion_forbidden",
    "runtime_id_policy": "singleton_only_for_v50",
    "singleton_runtime_id": "local_python_cli",
    "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
    "runtime_id_override_policy": "explicit_override_must_equal_singleton_case_sensitive_before_adapter_execution_else_fail_closed",
    "lane_pairing_policy": "for_each_declared_adapter_id_exactly_two_deployment_mode_rows_required_under_singleton_runtime_id",
    "lane_count_authority": "all_registry_rows_only_because_disabled_rows_are_forbidden",
    "empty_registry": "forbidden_fail_closed"
  },
  "parity_requirements": {
    "canonical_subtree_exact_match_required": true,
    "canonical_subtree_source_policy": "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only",
    "noncanonical_bundle_launcher_mode_difference_allowed": true,
    "bundle_launcher_difference_scope": "allowed_only_in_frozen_noncanonical_bundle_wrapper_surface",
    "policy_equivalence_exact_match_required": true,
    "policy_equivalence_required_keys": [
      "issue_code_set",
      "required_evidence_slots_filled",
      "allowlist_violations",
      "forbidden_effects_detected"
    ],
    "policy_equivalence_value_shapes": {
      "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
      "required_evidence_slots_filled": "boolean",
      "allowlist_violations": "lexicographically_sorted_unique_normalized_posix_path_list",
      "forbidden_effects_detected": "boolean"
    },
    "parity_extraction_source_policy": "typed_artifacts_and_deterministic_matrix_report_only_no_logs_repo_state_or_ad_hoc_reanalysis",
    "matrix_report_completeness_policy": "every_declared_lane_must_appear_exactly_once",
    "lane_specific_policy_override": "forbidden_fail_closed",
    "deterministic_parity_report_required": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v34b_matrix_parity_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "matrix_registry_path",
      "matrix_report_path",
      "matrix_report_hash",
      "lane_id_tuple",
      "enabled_row_policy",
      "lane_count_authority",
      "lane_count",
      "deployment_modes_covered",
      "adapter_ids_covered",
      "runtime_ids_covered",
      "singleton_runtime_id_enforced",
      "runtime_id_source_policy",
      "runtime_id_host_inference_forbidden",
      "declared_registry_only",
      "lexicographic_lane_order_enforced",
      "canonical_subtree_exact_match_required",
      "canonical_subtree_source_policy",
      "policy_equivalence_exact_match_required",
      "policy_equivalence_subject_keys_verified",
      "policy_equivalence_value_shapes_verified",
      "report_covers_all_declared_lanes",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v49",
      "notes"
    ]
  },
  "test_requirements": {
    "packaging_cross_mode_parity_guard_must_be_registry_backed": true,
    "runtime_id_singleton_enforced": true,
    "undeclared_lane_execution_forbidden": true,
    "duplicate_lane_tuple_rejected": true,
    "non_lexicographic_lane_order_rejected": true
  },
  "fail_closed_conditions": [
    "undeclared_matrix_lane_accepted",
    "disabled_or_ambiguous_matrix_lane_present",
    "duplicate_matrix_lane_tuple_accepted",
    "non_lexicographic_matrix_lane_order_accepted",
    "runtime_id_outside_frozen_singleton_accepted",
    "host_or_container_inferred_runtime_id_outside_singleton_accepted",
    "adapter_kind_outside_current_passthrough_set_accepted_by_matrix_registry",
    "canonical_subtree_parity_mismatch_accepted",
    "policy_equivalence_mismatch_accepted",
    "declared_matrix_lane_missing_or_duplicated_in_report",
    "non_authoritative_parity_source_accepted",
    "matrix_parity_evidence_missing_from_closeout"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## Y1) Declared Matrix-Lane Registry + Deterministic Parity-Report Baseline (`V34-B`)

### Goal

Make `V34-B` real as a declared registry/reporting contract over the matrix surfaces that
actually exist today.

### Scope

- define `adapter_matrix@1` as the authoritative finite lane registry for v50;
- define `adapter_matrix@1` as enabled-only in this arc; disabled rows are forbidden rather
  than advisory;
- require `adapter_matrix@1` adapter identifiers to reuse the declared
  `taskpack_runner_adapter_registry@1` namespace rather than invent a parallel adapter-id
  space;
- enumerate matrix lanes over current `deployment_mode x adapter_id` surfaces only;
- freeze `runtime_id` to a singleton declared value for this arc and require it to be
  contract-derived rather than host-inferred;
- emit deterministic `adapter_matrix_parity_report@1` output ordered by the frozen lane
  tuple;
- reuse existing packaging parity and policy-equivalence invariants rather than redefine
  them.

### Locks

- v50 must not claim full multi-runtime matrix support;
- `runtime_id` is a declared field in this arc but must remain exactly the frozen singleton
  value `local_python_cli`;
- `runtime_id` must be materialized only from the frozen contract value or an explicit
  parameter that case-sensitively exactly equals that value before any adapter execution;
  host, container, or environment inference is non-authoritative in v50;
- `adapter_matrix@1` is enabled-only for v50:
  - disabled rows are forbidden,
  - lane count and parity coverage derive from all registry rows only;
- matrix-lane membership must derive from declared registry rows only; runtime discovery or
  host inspection is non-authoritative;
- matrix adapter identifiers must resolve to already-declared runner adapter identifiers;
  `adapter_matrix@1` may project the existing runner registry into lane tuples but may not
  define a second adapter namespace;
- deployment mode enum remains exactly `adeu_integrated` and `standalone`;
- adapter kinds accepted by the matrix registry remain exactly the current passthrough set;
- registry tuple ordering must be lexicographic over
  `(deployment_mode, adapter_id, runtime_id)`;
- parity extraction must use only the schema-typed artifacts named in
  `preserved_authority_inputs` and the deterministic matrix report; logs, live repo state,
  and ad hoc re-analysis are non-authoritative for v50 parity decisions;
- canonical subtree parity must use the same frozen canonical artifact subject family already
  emitted by the packaging and verifier contracts; v50 does not authorize a new canonical
  projection;
- no matrix lane may relax existing runner, verifier, packaging, or v49 signing-handoff
  contracts;
- no new stop-gate metric keys are authorized in this path unless explicitly released in the
  corresponding lock doc.

### Acceptance

- matrix registry bytes are deterministic and schema-valid for identical inputs;
- matrix parity report bytes are deterministic and schema-valid for identical inputs;
- each declared adapter id has exactly two released deployment-mode rows under the frozen
  singleton runtime id;
- identical logical runs keep the same declared singleton runtime id even when executed in
  different host/container wrappers, unless a future lock explicitly expands the runtime lane
  set;
- every declared lane must appear exactly once in the deterministic matrix report;
- undeclared, duplicate, or out-of-order lanes fail closed.

## Y2) Matrix-Lane Guard Suite + Current-Lane Parity Enforcement (`V34-B`)

### Goal

Prove that the registry-backed matrix baseline preserves existing current-lane parity and
policy-equivalence guarantees.

### Scope

- make current cross-mode parity tests consume the declared matrix lane contract;
- add deterministic guard coverage for duplicate tuple rejection, ordering rejection,
  singleton runtime-id enforcement, and undeclared lane rejection;
- require exact canonical subtree parity and exact policy-equivalence parity per declared
  adapter id across integrated and standalone lanes;
- integrate canonical matrix parity evidence into the closeout surface.

### Locks

- canonical parity comparison must remain over the canonical emitted subtree; deployment-mode
  launcher difference is permitted only in the already-frozen non-canonical bundle wrapper
  surface; no canonical emitted artifact semantics may differ by deployment mode;
- canonical parity comparison must use the same frozen canonical artifact subject family
  already used by the packaging and verifier contracts; v50 does not authorize a new
  canonical projection;
- policy-equivalence comparison must remain exact-match over the frozen subject keys;
- policy-equivalence value shapes remain frozen:
  - `issue_code_set` is a lexicographically sorted unique string list in canonical form,
  - `required_evidence_slots_filled` is boolean,
  - `allowlist_violations` is a lexicographically sorted unique normalized posix-path list,
  - `forbidden_effects_detected` is boolean;
- closeout evidence must bind to the deterministic matrix report by hash and must prove the
  exact frozen policy-equivalence subject keys that were verified;
- every declared lane must appear exactly once in the matrix report; missing or duplicated
  report rows fail closed;
- lane-specific policy overrides and lane-specific semantics are forbidden;
- closeout proof must distinguish between the declared matrix registry, the parity report,
  and the stop-gate continuity artifacts;
- runtime-observability evidence remains required and informational-only.

### Acceptance

- registry-backed parity guards remain green for current released lanes;
- parity fails closed on canonical subtree drift or policy-equivalence drift;
- closeout path emits the required `v34b_matrix_parity_evidence@1` block;
- deterministic guard suites remain green under frozen environment requirements.

## Stop-Gate Impact (v50)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v50 closeout must include runtime-observability comparison row against v49 baseline.
- v50 closeout must include metric-key continuity assertion against v49 baseline.
- v50 closeout must include matrix-parity evidence block:
  - block schema is docs-only `v34b_matrix_parity_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact and included in the canonical closeout path,
  - required keys are:
    - `schema`
    - `contract_source`
    - `matrix_registry_path`
    - `matrix_report_path`
    - `matrix_report_hash`
    - `lane_id_tuple`
    - `enabled_row_policy`
    - `lane_count_authority`
    - `lane_count`
    - `deployment_modes_covered`
    - `adapter_ids_covered`
    - `runtime_ids_covered`
    - `singleton_runtime_id_enforced`
    - `runtime_id_source_policy`
    - `runtime_id_host_inference_forbidden`
    - `declared_registry_only`
    - `lexicographic_lane_order_enforced`
    - `canonical_subtree_exact_match_required`
    - `canonical_subtree_source_policy`
    - `policy_equivalence_exact_match_required`
    - `policy_equivalence_subject_keys_verified`
    - `policy_equivalence_value_shapes_verified`
    - `report_covers_all_declared_lanes`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v49`
    - `notes`

## Error/Exit Policy (v50)

- No new URM runtime error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v50 introduces new matrix-lane harness diagnostics, they must be constrained to an
  authoritative `AHK50xx` registry and remain error-only with non-zero exit behavior.
- If v50 introduces new matrix-lane diagnostics, deterministic issue ordering must sort by
  `(issue_code, lane_tuple, artifact_path)`.
- for that ordering rule, `lane_tuple` serializes in the frozen field order
  `(deployment_mode, adapter_id, runtime_id)` and `artifact_path` remains repo-relative
  posix.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v34b declared matrix registry and parity report baseline`
2. `tests: add v34b matrix-lane parity and registry guard suite`

## Intermediate Preconditions (for v50 start)

1. v49 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v49 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md`
3. Existing v49 signing/handoff completion remains available at v50 start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_signature.py`
   - `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json`
4. Existing deployment-mode parity and adapter-registry surfaces remain available at v50
   start:
   - `packages/adeu_agent_harness/src/adeu_agent_harness/package_ux.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/run_taskpack.py`
   - `packages/adeu_agent_harness/src/adeu_agent_harness/verify_taskpack_run.py`
5. Existing v49 closeout artifacts remain available at v50 start:
   - `artifacts/quality_dashboard_v49_closeout.json`
   - `artifacts/stop_gate/metrics_v49_closeout.json`
   - `artifacts/stop_gate/report_v49_closeout.md`
   - `artifacts/agent_harness/v49/evidence_inputs/runtime_observability_comparison_v49.json`
   - `artifacts/agent_harness/v49/evidence_inputs/metric_key_continuity_assertion_v49.json`
6. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
7. No additional `L2` boundary release beyond v49 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `Y1` and `Y2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V34-B` matrix baseline is declared only over current released surfaces and does not claim
  unsupported multi-runtime expansion.
- v50 closeout evidence includes runtime-observability comparison row against v49 baseline,
  metric-key continuity assertion against v49 baseline, and
  `v34b_matrix_parity_evidence@1`.
- registry-backed parity guards prove exact canonical subtree parity and exact
  policy-equivalence parity across current released lanes.
- v36-v49 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
