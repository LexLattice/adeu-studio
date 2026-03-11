# Locked Continuation vNext+57 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS56.md`
- `docs/ASSESSMENT_vNEXT_PLUS56_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 11, 2026 UTC).

## Decision Basis

- `vNext+56` (`V35-A`, `A1`/`A2`) is merged on `main` with green CI checks.
- `vNext+56` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS56.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS56_EDGES.md` marks the `V35-A` state-materialization family as
  closed and restores eligibility for a fresh delegation/handoff slice.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md` now names `V35-B` as the next default candidate after
  `V35-A` closure.
- current repo reality is narrower than a full delegated-builder execution lane:
  - `packages/urm_runtime/src/urm_runtime/orchestration_state.py` and
    `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py` now provide released
    canonical orchestration-state and closeout-evidence foundations,
  - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`,
    `packages/urm_runtime/src/urm_runtime/child_workflow.py`, and
    `packages/urm_runtime/src/urm_runtime/child_recovery.py` already provide generic child
    dispatch/workflow/recovery foundations,
  - `packages/urm_runtime/src/urm_runtime/models.py` already exposes `AgentSpawnRequest`,
    `AgentSpawnResponse`, steer/session models, and normalized `urm-events@1`,
  - `packages/urm_runtime/src/urm_runtime/copilot.py` already persists child runs,
    dispatch tokens, budgets, and canonical state artifacts over current runtime state,
  - no released `builder_worker` role exists in `urm_runtime.roles.ROLE_REGISTRY`,
  - no released scoped delegation request surface records canonical scope kind, requested
    worker role, or delegation task kind,
  - no released non-empty reconciled `role_handoff_envelope@1` entries exist on `main`,
  - no released explicit orchestrator reconciliation step exists for child outputs,
  - no released `v35b_delegation_handoff_evidence@1` closeout block exists on `main`,
  - no worker transcript visibility, topology UX, or runtime enforcement promotion is
    released on `main`.
- `vNext+57` therefore selects one thin `V35-B` baseline slice only:
  - single-builder delegation over the now-canonical v56 orchestration-state substrate,
  - typed delegated scope and role recording,
  - reconciled handoff emission and closeout evidence integration,
  - no transcript visibility, topology UX, multi-writer release, or runtime enforcement in
    this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v57,
  - v57 keyset must be exactly equal to v56 keyset,
  - baseline derived cardinality at v57 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v57 is explicit and narrow:
  - this arc authorizes one `L1` delegation/handoff release lane only,
  - no `L2` boundary release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond `main_orchestrator`,
  - no multi-builder or multi-writer release is authorized in this arc.
- `V35-A` state artifacts and evidence surfaces remain frozen prerequisites and are not
  redefined by this arc.
- The multi-role constitution remains a frozen prerequisite input:
  - `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json` remains the canonical draft contract
    surface,
  - `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md` and
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md` remain derived interpretive inputs,
  - this arc may implement the `V35-B` baseline only and may not widen the constitutional
    surface beyond those draft artifacts.
- `V35-B` release-shape lock for v57 is frozen:
  - this arc is a single-builder delegation and reconciled handoff slice only,
  - delegation, lease, handoff, and reconciliation logic must prefer
    `packages/urm_runtime` or an explicit new orchestration surface rather than silent
    accretion into `packages/adeu_agent_harness`,
  - worker transcript visibility, topology UX, and runtime enforcement remain out of scope
    for this arc,
  - no direct worker-to-user authority surface is authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `B1` Single-builder delegation role/scope/lease baseline (`V35-B`)
2. `B2` Reconciled handoff evidence + guard suite (`V35-B`)

Out-of-scope note:

- worker transcript visibility or transcript-derived UX in this arc,
- dynamic topology/duty map UX in this arc,
- runtime enforcement of the constitutional fail-closed conditions in this arc,
- multi-builder or multi-writer execution in this arc,
- direct user-to-worker interaction beyond orchestrator mediation in this arc,
- closeout hardening bundle (`O1`/`O2`/`O3`) implementation in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v57)

- v58+ `V35-C` worker transcript and progress visibility
- v59+ `V35-D` dynamic topology/duty map UX
- v60+ `V35-E` runtime enforcement and promotion hardening
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- multi-builder execution, direct worker/user interaction, stronger write-lease
  mechanisms, and broader authority-surface hardening remain deferred follow-ons under
  `docs/FUTURE_CLEANUPS.md`

## V56 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md",
  "target": "V35-B-baseline",
  "required_continuity_guards": [
    "V35_A_A1_ORCHESTRATION_STATE_BASELINE_GREEN",
    "V35_A_A2_ORCHESTRATION_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v56_v35a_state_and_evidence_contracts_remain_frozen_while_v35b_single_builder_delegation_and_reconciled_handoffs_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v57.
- this narrowed machine-checkable consumption block is v56-local only and does not weaken
  the global continuity locks declared above; v36-v56 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V35-B Delegation/Handoff Contract (Machine-Checkable)

```json
{
  "schema": "v35b_delegation_handoff_contract@1",
  "target_arc": "vNext+57",
  "target_path": "V35-B",
  "preserved_authority_inputs": {
    "v35a_state_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1",
    "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
    "multi_role_lock_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md",
    "multi_role_policy_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md",
    "normalized_event_schema": "urm-events@1",
    "agent_spawn_request_model": "AgentSpawnRequest",
    "agent_spawn_response_model": "AgentSpawnResponse",
    "role_policy_registry": "urm_runtime.roles.ROLE_REGISTRY",
    "child_workflow_entrypoint": "urm_runtime.child_workflow.run_child_workflow_v2",
    "worker_run_storage": "urm_worker_run",
    "dispatch_token_storage": "urm_dispatch_token",
    "v35a_orchestration_state_evidence": "required_frozen_precondition"
  },
  "delegation_requirements": {
    "builder_role_identifier": "builder_worker",
    "support_role_enum": [
      "explorer",
      "validator",
      "docs_helper"
    ],
    "support_role_exercise_policy": "at_least_one_released_support_role_path_proven_not_all_enumerated_support_roles_required_to_be_exercised",
    "requested_role_field_required": true,
    "granted_role_field_required": true,
    "delegation_task_kind_field_required": true,
    "delegated_scope_descriptor_required": true,
    "delegated_scope_kind_enum": [
      "repo_wide",
      "subtree",
      "module_set",
      "file_set",
      "artifact_surface_only"
    ],
    "one_builder_default_required": true,
    "builder_write_lease_transfer_policy": "explicit_main_orchestrator_only",
    "authoritative_builder_write_lease_required_for_write_tasks": true,
    "support_workers_non_authoritative_by_default": true,
    "support_worker_surface_policy": "advisory_or_scratch_only_by_default_unless_explicitly_re_roled",
    "worker_direct_user_boundary_forbidden": true,
    "delegation_request_truth_policy": "delegation_requests_record_intent_only_not_accepted_effects_without_runtime_execution_and_reconciliation",
    "claimed_work_presence_fields": [
      "files_changed",
      "commands_run",
      "artifacts_produced",
      "evidence_refs"
    ],
    "completed_child_handoff_entry_required_when_claimed_work_present": true,
    "zero_occurrence_empty_artifacts_required": [
      "role_transition_record@1",
      "role_handoff_envelope@1"
    ],
    "zero_occurrence_empty_artifact_policy": "deterministic_canonical_empty_artifacts_emitted_not_omitted",
    "handoff_reconciliation_required": true,
    "unreconciled_worker_output_non_authoritative": true,
    "reconciliation_minimum_checks": [
      "verify_requested_role_and_granted_role_are_recorded",
      "verify_scope_descriptor_kind_is_present_and_valid",
      "verify_evidence_refs_resolve_to_actual_outputs",
      "verify_handoff_claimed_files_changed_or_commands_run_match_materialized_child_outputs_or_runtime_records",
      "reject_child_claims_as_authoritative_without_explicit_orchestrator_reconciliation"
    ],
    "execution_state_source_policy": "derived_from_urm_runtime_session_worker_dispatch_event_and_handoff_state_only_no_ad_hoc_ui_inference"
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v35b_delegation_handoff_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "orchestration_state_snapshot_path",
      "orchestration_state_snapshot_hash",
      "write_lease_state_path",
      "write_lease_state_hash",
      "role_transition_record_path",
      "role_transition_record_hash",
      "role_handoff_envelope_path",
      "role_handoff_envelope_hash",
      "builder_role_materialized",
      "support_roles_materialized",
      "delegated_scope_kind_recorded",
      "single_builder_default_enforced",
      "support_workers_non_authoritative",
      "handoff_artifact_materialized",
      "handoff_reconciliation_required",
      "unreconciled_worker_output_non_authoritative",
      "worker_direct_user_boundary_forbidden",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v56",
      "zero_occurrence_empty_artifacts_materialized",
      "notes"
    ]
  },
  "test_requirements": {
    "builder_role_recorded": true,
    "at_least_one_support_role_path_recorded": true,
    "delegated_scope_kind_recorded": true,
    "single_builder_write_lease_enforced": true,
    "completed_child_handoff_entry_materialized": true,
    "zero_occurrence_empty_artifacts_materialized": true,
    "handoff_reconciliation_required": true,
    "support_workers_non_authoritative": true,
    "worker_direct_user_boundary_forbidden": true,
    "v35b_delegation_handoff_evidence_deterministic": true
  },
  "fail_closed_conditions": [
    "requested_role_missing",
    "requested_role_invalid",
    "granted_role_missing",
    "delegated_scope_descriptor_missing_or_invalid",
    "delegation_task_kind_missing",
    "multiple_authoritative_builders_active_by_default",
    "builder_write_lease_missing_for_authoritative_write_task",
    "role_transition_record_missing_or_omitted",
    "role_handoff_envelope_missing_or_omitted",
    "zero_occurrence_empty_artifact_missing_or_noncanonical",
    "completed_child_handoff_entry_missing_when_claimed_work_present",
    "worker_output_treated_as_accepted_truth_without_reconciliation",
    "support_worker_authority_drift_without_explicit_rerole",
    "worker_direct_user_boundary_established"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

Interpretive notes:

- `support_roles_materialized` means the bounded support-role surface is released and at
  least one support-worker path is proven in v57; it does not require every enumerated
  support role to be exercised in this arc.
- `handoff_artifact_materialized` means the canonical handoff artifact exists in all
  cases and is non-empty if and only if claimed work is present.
- `write_lease_state@1` proves current authoritative write ownership for the delegated
  lane.
- `role_transition_record@1` proves authority-surface transitions and explicit re-roles.
- zero-occurrence transition or handoff cases still require deterministic empty canonical
  artifacts rather than omission.

## B1) Single-Builder Delegation Role/Scope/Lease Baseline (`V35-B`)

### Goal

Make `V35-B` real as one delegated builder plus bounded support workers over the now-frozen
v56 orchestration-state substrate.

### Scope

- extend delegated child-run recording to carry:
  - requested role,
  - granted role,
  - delegation task kind,
  - canonical delegated scope descriptor;
- release one authoritative `builder_worker` role and a bounded non-authoritative
  support-role surface:
  - `explorer`
  - `validator`
  - `docs_helper`
  - v57 must prove at least one bounded support-worker path; it does not need to exercise
    every listed support role;
- require explicit write-lease transfer state when the delegated builder is expected to
  perform authoritative implementation work;
- treat `write_lease_state@1` as the proof of current authoritative write ownership and
  `role_transition_record@1` as the proof of authority-surface transitions or re-roles;
- keep support workers advisory or scratch-only by default unless explicitly re-roled;
- materialize non-empty `role_handoff_envelope@1` entries when completed delegated work
  claims work in any non-empty `files_changed`, `commands_run`, `artifacts_produced`, or
  `evidence_refs` field;
- require deterministic empty canonical `role_transition_record@1` and
  `role_handoff_envelope@1` artifacts when no transition or no handoff occurs rather than
  treating omission as valid;
- keep worker output non-authoritative until explicit orchestrator reconciliation;
- keep the main orchestrator as the sole user-facing authority surface.

### Locks

- v57 must not release worker transcript visibility or topology UX.
- v57 must not release runtime enforcement beyond state/handoff materialization and guard
  checks.
- only one authoritative builder write lease may be active by default.
- support workers remain non-authoritative by default and may not silently acquire builder
  or governance authority.
- worker outputs remain advisory until reconciled.
- delegated scope must be recorded with explicit scope kind rather than free-form scope
  text only.
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

### Acceptance

- the orchestrator can run one end-to-end delegated implementation loop with:
  - one authoritative builder write lease on a write task,
  - at least one bounded support-worker path that remains non-authoritative,
  - typed delegated scope recording,
  - one reconciled completed child handoff when claimed work is present,
  - deterministic empty transition/handoff artifacts in zero-occurrence cases,
  - explicit orchestrator reconciliation,
  - no authority drift.

## B2) Reconciled Handoff Evidence + Guard Suite (`V35-B`)

### Goal

Use the delegated-builder and handoff surfaces as an actual closeout-grade evidence lane
and prove the constitutional delegation invariants hold under the current narrow scope.

### Scope

- add canonical closeout evidence for the `V35-B` delegation/handoff lane;
- add deterministic guard coverage for:
  - missing or invalid requested/granted roles,
  - missing or invalid delegated scope kind,
  - missing builder write lease on authoritative write tasks,
  - multiple authoritative builders by default,
  - missing deterministic empty transition/handoff artifacts when zero-occurrence cases
    apply,
  - missing handoff entries for completed claimed work,
  - unreconciled worker output being treated as accepted truth,
  - support-worker authority drift,
  - worker direct user-boundary violations;
- keep the lane strictly pre-visibility and pre-enforcement.

### Locks

- evidence is closeout-authoritative only via deterministic artifact hashes.
- the `V35-B` evidence lane must not redefine transcript visibility, topology UX, or
  runtime enforcement semantics.
- closeout proof must distinguish between:
  - delegated child-run request/lease state,
  - authority-surface transition state,
  - typed handoff emission,
  - orchestrator reconciliation,
  - docs-side `v35b_delegation_handoff_evidence@1`.
- `write_lease_state@1` proves current authoritative write ownership, while
  `role_transition_record@1` proves authority-surface transitions and explicit re-roles.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v35b_delegation_handoff_evidence@1` block;
- deterministic guard suites prove the single-builder default and worker-boundary posture
  remain intact;
- completed delegated work emits typed handoff entries and explicit reconciliation
  requirement rather than relying on raw worker output alone;
- zero-occurrence transition/handoff cases still materialize deterministic empty canonical
  artifacts rather than relying on omission;
- no transcript visibility or topology UX surface is required for the arc to pass.

## Stop-Gate Impact (v57)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v57 closeout must include runtime-observability comparison row against v56 baseline.
- v57 closeout must include metric-key continuity assertion against v56 baseline.
- v57 closeout must include delegation/handoff evidence block:
  - block schema is docs-only `v35b_delegation_handoff_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a
    deterministic JSON evidence input artifact, included in the canonical closeout path,
    and treated as closeout-authoritative only after implementation,
  - `support_roles_materialized` means the support-role surface is released and at least
    one bounded support-worker path is proven; it does not require all enumerated support
    roles to be exercised,
  - `write_lease_state@1` proves current authoritative write ownership, while
    `role_transition_record@1` proves authority-surface transitions and explicit re-roles,
  - required keys are:
    - `schema`
    - `contract_source`
    - `evidence_input_path`
    - `orchestration_state_snapshot_path`
    - `orchestration_state_snapshot_hash`
    - `write_lease_state_path`
    - `write_lease_state_hash`
    - `role_transition_record_path`
    - `role_transition_record_hash`
    - `role_handoff_envelope_path`
    - `role_handoff_envelope_hash`
    - `builder_role_materialized`
    - `support_roles_materialized`
    - `delegated_scope_kind_recorded`
    - `single_builder_default_enforced`
    - `support_workers_non_authoritative`
    - `handoff_artifact_materialized`
    - `handoff_reconciliation_required`
    - `unreconciled_worker_output_non_authoritative`
    - `worker_direct_user_boundary_forbidden`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v56`
    - `zero_occurrence_empty_artifacts_materialized`
    - `notes`

## Error/Exit Policy (v57)

- No new stop-gate error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v57 introduces delegation/handoff diagnostics, they must remain deterministic,
  error-only, and fail closed on invalid inputs.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v35b delegation and handoff baseline`
2. `tests: add v35b delegation evidence and guard suite`

## Intermediate Preconditions (for v57 start)

1. v56 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v56 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS56.md`
3. Existing `V35-A` closeout artifacts remain available at v57 start:
   - `artifacts/quality_dashboard_v56_closeout.json`
   - `artifacts/stop_gate/metrics_v56_closeout.json`
   - `artifacts/stop_gate/report_v56_closeout.md`
   - `artifacts/agent_harness/v56/evidence_inputs/v35a_orchestration_state_evidence_v56.json`
4. Existing `urm_runtime` foundations remain available at v57 start:
   - `packages/urm_runtime/src/urm_runtime/models.py`
   - `packages/urm_runtime/src/urm_runtime/roles.py`
   - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
   - `packages/urm_runtime/src/urm_runtime/child_workflow.py`
   - `packages/urm_runtime/src/urm_runtime/child_recovery.py`
   - `packages/urm_runtime/src/urm_runtime/storage.py`
   - `packages/urm_runtime/src/urm_runtime/orchestration_state.py`
   - `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py`
   - `packages/urm_runtime/src/urm_runtime/copilot.py`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v56 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `B1` and `B2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V35-B` closes the delegated single-builder and reconciled-handoff gap without widening
  into transcript visibility, topology UX, or runtime enforcement.
- v57 closeout evidence includes runtime-observability comparison row against v56 baseline,
  metric-key continuity assertion against v56 baseline, and
  `v35b_delegation_handoff_evidence@1`.
- delegated scope, role, lease, and handoff state are deterministic and sufficient to
  reconstruct the current builder/support delegation posture and reconciliation status.
- support-worker outputs remain non-authoritative until explicit orchestrator
  reconciliation.
- v36-v56 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
