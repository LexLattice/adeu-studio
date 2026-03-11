# Locked Continuation vNext+56 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md`
- `docs/ASSESSMENT_vNEXT_PLUS55_EDGES.md`
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

- `vNext+55` (`V34-G`, `D1`/`D2`) is merged on `main` with green CI checks.
- `vNext+55` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS55_EDGES.md` marks the `V34-A` through `V34-G` family as
  closed and restores eligibility for a fresh post-`V34` planning family.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md` names `V35-A` as the next default candidate after
  `V34` closure.
- current repo reality is narrower than a full multi-role orchestration UX lane:
  - `packages/urm_runtime/src/urm_runtime/roles.py` already defines role-policy registry
    foundations,
  - `packages/urm_runtime/src/urm_runtime/child_dispatch.py` and
    `packages/urm_runtime/src/urm_runtime/storage.py` already provide child dispatch,
    queue, and lease-token persistence foundations,
  - `packages/urm_runtime/src/urm_runtime/models.py` already defines `urm-events@1`,
    `AgentSpawnRequest`, `AgentSpawnResponse`, and related session/worker models,
  - `packages/urm_runtime/src/urm_runtime/events_tools.py` already validates and replays
    normalized URM event streams,
  - `packages/urm_runtime/src/urm_runtime/copilot.py` already persists and replays session
    and worker event state,
  - no released `orchestration_state_snapshot@1` artifact exists on `main`,
  - no released `execution_topology_state@1` artifact exists on `main`,
  - no released `write_lease_state@1` artifact exists on `main`,
  - no released `role_transition_record@1` artifact exists on `main`,
  - no released `role_handoff_envelope@1` artifact exists on `main`,
  - no released `v35a_orchestration_state_evidence@1` closeout block exists on `main`,
  - no worker transcript visibility or topology UX is released on `main`,
  - no runtime enforcement of the draft multi-role constitution is released on `main`.
- `vNext+56` therefore selects one thin `V35-A` baseline slice only:
  - canonical orchestration-state artifacts over current `urm_runtime` foundations,
  - deterministic session/event identity, scope-kind, write-lease, role-transition, and
    handoff-state materialization,
  - canonical closeout evidence integration plus guard coverage,
  - no worker transcript visibility, topology UI, multi-writer release, or runtime
    enforcement in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md` remain authoritative for baseline continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v56,
  - v56 keyset must be exactly equal to v55 keyset,
  - baseline derived cardinality at v56 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v56 is explicit and narrow:
  - this arc authorizes one `L1` orchestration-state release lane only,
  - no `L2` boundary release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority surface and no new authority-bearing persistence surface
    beyond the canonical state artifacts authorized here are released in this arc.
- `V34-A` through `V34-G` remain frozen prerequisites and are not redefined by this arc.
- The multi-role constitution remains a frozen prerequisite input:
  - `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json` remains the canonical draft contract
    surface,
  - `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md` and
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md` remain derived interpretive inputs,
  - this arc may implement the `V35-A` baseline only and may not widen the constitutional
    surface beyond those draft artifacts.
- `V35-A` release-shape lock for v56 is frozen:
  - this arc is a canonical orchestration-state and evidence slice only,
  - orchestration-state, delegation, event-lineage, and lease-state logic must prefer
    `packages/urm_runtime` or an explicit new orchestration surface rather than silent
    accretion into `packages/adeu_agent_harness`,
  - worker transcript visibility, topology UX, and runtime enforcement remain out of scope
    for this arc,
  - no multi-writer release is authorized in this arc,
  - no direct worker-to-user authority surface is authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `A1` Canonical orchestration-state schemas + session/event identity baseline (`V35-A`)
2. `A2` Canonical orchestration evidence + guard suite (`V35-A`)

Out-of-scope note:

- single-builder delegation execution loop beyond the orchestration-state baseline in this
  arc,
- worker transcript visibility or transcript-derived UX in this arc,
- dynamic topology/duty map UX in this arc,
- runtime enforcement of the constitutional fail-closed conditions in this arc,
- multi-writer or split-lease execution in this arc,
- direct user-to-worker interaction beyond orchestrator mediation in this arc,
- closeout hardening bundle (`O1`/`O2`/`O3`) implementation in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v56)

- v57+ `V35-B` single-builder delegation and reconciled worker handoff execution
- v58+ `V35-C` worker transcript and progress visibility
- v59+ `V35-D` dynamic topology/duty map UX
- v60+ `V35-E` runtime enforcement and promotion hardening
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- multi-writer execution, direct worker/user interaction, stronger write-lease mechanisms,
  and builder dry-run execution remain deferred follow-ons under
  `docs/FUTURE_CLEANUPS.md`

## V55 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS55.md",
  "target": "V35-A-baseline",
  "required_continuity_guards": [
    "V34_G_D1_REMOTE_ENCLAVE_BASELINE_GREEN",
    "V34_G_D2_REMOTE_ENCLAVE_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v55_v34_family_closeout_contracts_remain_frozen_while_v35a_orchestration_state_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v56.
- this narrowed machine-checkable consumption block is v55-local only and does not weaken
  the global continuity locks declared above; v36-v55 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V35-A Orchestration-State Contract (Machine-Checkable)

```json
{
  "schema": "v35a_orchestration_state_contract@1",
  "target_arc": "vNext+56",
  "target_path": "V35-A",
  "preserved_authority_inputs": {
    "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
    "multi_role_lock_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md",
    "multi_role_policy_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md",
    "normalized_event_schema": "urm-events@1",
    "agent_spawn_response_model": "AgentSpawnResponse",
    "role_policy_registry": "urm_runtime.roles.ROLE_REGISTRY",
    "worker_run_storage": "urm_worker_run",
    "dispatch_token_storage": "urm_dispatch_token",
    "v34g_remote_enclave_contract": "required_frozen_precondition"
  },
  "state_scope_requirements": {
    "orchestration_state_snapshot_schema": "orchestration_state_snapshot@1",
    "execution_topology_state_schema": "execution_topology_state@1",
    "write_lease_state_schema": "write_lease_state@1",
    "role_transition_record_schema": "role_transition_record@1",
    "role_handoff_envelope_schema": "role_handoff_envelope@1",
    "shared_orchestration_state_builder_required": true,
    "orchestration_foundation_package": "packages/urm_runtime",
    "pipeline_package_accretion_policy": "forbidden_without_explicit_decomposition_or_lock_text",
    "control_plane_owner": "main_orchestrator",
    "single_writer_default_required": true,
    "worker_direct_user_boundary_forbidden": true,
    "support_worker_surface_policy": "advisory_or_scratch_only_by_default_unless_explicitly_re_roled",
    "canonical_orchestration_identity_fields": [
      "orchestrator_session_id",
      "worker_session_id",
      "parent_session_id",
      "event_cursor",
      "last_reconciled_event",
      "continuation_bridge_ref"
    ],
    "worker_session_identity_scope_policy": "v56_baseline_records_current_or_active_worker_session_identity_only_not_complete_multiworker_lineage",
    "continuation_bridge_ref_scope_policy": "v56_baseline_records_current_or_latest_bridge_ref_needed_for_current_orchestration_state_not_full_future_multiworker_bridge_graph",
    "runtime_event_truth_policy": "runtime_events_are_source_surfaces_only_not_accepted_truth_without_canonical_reconciliation_or_explicit_governance_acceptance",
    "compaction_lineage_policy": "show_compaction_seams_and_bridge_linked_continuity_explicitly_no_silent_flattening",
    "scope_granularity_enum": [
      "repo_wide",
      "subtree",
      "module_set",
      "file_set",
      "artifact_surface_only"
    ],
    "execution_topology_state_policy": "reconciliation_and_state_artifact_only_not_rendered_ux_graph",
    "handoff_trust_model": "self_report_non_authoritative_until_reconciled",
    "role_transition_zero_occurrence_policy": "deterministic_empty_artifact_required_when_no_transition_occurs",
    "role_handoff_zero_occurrence_policy": "deterministic_empty_artifact_required_when_no_handoff_occurs",
    "handoff_required_field_empty_value_policies": {
      "escalation_reason": "required_field_uses_null_when_no_escalation_exists",
      "blockers": "required_field_uses_empty_array_when_none_exist",
      "files_changed": "required_field_uses_empty_array_when_none_exist",
      "commands_run": "required_field_uses_empty_array_when_none_exist",
      "artifacts_produced": "required_field_uses_empty_array_when_none_exist",
      "evidence_refs": "required_field_uses_empty_array_when_none_exist",
      "open_risks": "required_field_uses_empty_array_when_none_exist"
    },
    "handoff_required_fields": [
      "role",
      "authority_level",
      "authority_domain",
      "artifact_class",
      "artifact_surface",
      "repo_root",
      "branch_or_head",
      "scope_owned",
      "scope_remaining",
      "files_changed",
      "commands_run",
      "artifacts_produced",
      "evidence_refs",
      "status",
      "blocking_state",
      "blockers",
      "open_risks",
      "escalation_reason",
      "recommended_next_action"
    ],
    "reconciliation_minimum_checks": [
      "recompute_effective_files_changed_from_observed_repo_state",
      "compare_claimed_scope_owned_to_observed_mutation_surface",
      "verify_evidence_refs_resolve_to_actual_outputs",
      "reject_lease_scope_sufficiency_claims_based_on_self_report_alone"
    ],
    "execution_state_source_policy": "derived_from_urm_runtime_session_worker_dispatch_and_event_state_only_no_ad_hoc_ui_inference"
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v35a_orchestration_state_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "orchestration_state_snapshot_path",
      "orchestration_state_snapshot_hash",
      "execution_topology_state_path",
      "execution_topology_state_hash",
      "write_lease_state_path",
      "write_lease_state_hash",
      "role_transition_record_path",
      "role_transition_record_hash",
      "role_handoff_envelope_path",
      "role_handoff_envelope_hash",
      "orchestration_foundation_package",
      "single_writer_default_enforced",
      "worker_direct_user_boundary_forbidden",
      "canonical_identity_fields_recorded",
      "last_reconciled_event_recorded",
      "continuation_bridge_ref_recorded",
      "zero_occurrence_empty_artifacts_materialized",
      "scope_granularity_enum_frozen",
      "handoff_reconciliation_required",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v55",
      "notes"
    ]
  },
  "test_requirements": {
    "orchestration_state_snapshot_deterministic": true,
    "execution_topology_state_deterministic": true,
    "write_lease_state_deterministic": true,
    "role_transition_empty_artifact_deterministic_when_absent": true,
    "role_handoff_empty_artifact_deterministic_when_absent": true,
    "handoff_empty_value_encoding_deterministic": true,
    "write_lease_single_writer_default_enforced": true,
    "role_transition_record_required_for_authority_change": true,
    "handoff_envelope_missing_field_rejected": true,
    "compaction_lineage_recorded": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "fail_closed_conditions": [
    "orchestration_state_snapshot_missing",
    "execution_topology_state_missing",
    "write_lease_state_missing",
    "role_transition_record_missing",
    "role_handoff_envelope_missing",
    "multiple_authoritative_writers_active_by_default",
    "worker_direct_user_boundary_established",
    "runtime_event_stream_treated_as_accepted_truth_without_reconciliation",
    "compaction_lineage_silently_flattened",
    "scope_granularity_missing_or_invalid",
    "handoff_required_field_missing_or_invalid",
    "handoff_required_empty_value_policy_violated",
    "lease_scope_sufficiency_accepted_from_self_report_alone"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

## A1) Canonical Orchestration-State Schemas + Session/Event Identity Baseline (`V35-A`)

### Goal

Make `V35-A` real as canonical orchestration state over current `urm_runtime` foundations
rather than draft constitutional prose only.

### Scope

- define deterministic canonical artifacts for:
  - orchestration-state snapshot,
  - execution topology state,
  - write-lease state,
  - role-transition record,
  - role-handoff envelope;
- bind orchestration state to the frozen session/event identity field set;
- treat `worker_session_id` and `continuation_bridge_ref` as current-state baseline fields
  for v56 rather than claims of full future multiworker lineage coverage;
- materialize compaction lineage through explicit `continuation_bridge_ref` handling rather
  than silent pre/post-compaction flattening;
- freeze scope-kind reporting to the declared enum set;
- require deterministic empty `role_transition_record@1` and `role_handoff_envelope@1`
  artifacts when no transition or no handoff occurs rather than treating absence as valid;
- require deterministic canonical empty-value encoding for required handoff fields that are
  not applicable in the current state;
- keep the main orchestrator as the sole user-facing authority surface.

### Locks

- v56 must not release worker transcript visibility or topology UX.
- v56 must not release runtime enforcement beyond canonical state materialization and guard
  checks.
- runtime events are source surfaces only; they do not become accepted truth without
  canonical reconciliation or explicit governance acceptance.
- `execution_topology_state@1` is a reconciliation/state artifact only in this arc, not a
  rendered UX graph or topology view.
- support workers remain non-authoritative by default and may emit advisory or scratch
  surfaces only unless explicitly re-roled.
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

### Acceptance

- identical inputs produce deterministic orchestration-state artifact bytes across reruns;
- identical inputs produce deterministic `v35a_orchestration_state_evidence@1` bytes across
  reruns;
- canonical state is sufficient to reconstruct current roles, lease holder, scopes, current
  orchestrator/worker session identity, reconciliation cursor, and compaction linkage;
- worker direct user-boundary release does not occur in this path.

## A2) Canonical Orchestration Evidence + Guard Suite (`V35-A`)

### Goal

Use the orchestration-state artifacts as an actual closeout-grade evidence surface and prove
the baseline constitutional invariants hold under the current narrow scope.

### Scope

- add canonical closeout evidence for the `V35-A` orchestration lane;
- add deterministic guard coverage for:
  - missing orchestration-state artifacts,
  - missing or malformed handoff fields,
  - missing role-transition records on authority change,
  - missing compaction lineage linkage,
  - multiple-writer default violations,
  - worker direct user-boundary violations;
- keep the lane strictly pre-visibility and pre-enforcement.

### Locks

- evidence is closeout-authoritative only via deterministic artifact hashes.
- the `V35-A` evidence lane must not redefine worker transcript visibility, topology UX, or
  runtime enforcement semantics.
- closeout proof must distinguish between:
  - orchestration-state artifacts,
  - handoff/state reconciliation,
  - docs-side `v35a_orchestration_state_evidence@1`.
- runtime-observability evidence remains required and informational-only.

### Acceptance

- closeout path emits the required `v35a_orchestration_state_evidence@1` block;
- deterministic guard suites prove the single-writer default and worker-boundary posture
  remain intact;
- zero-occurrence transition/handoff cases still materialize deterministic empty canonical
  artifacts rather than relying on omission;
- no worker visibility or topology UX surface is required for the arc to pass.

## Stop-Gate Impact (v56)

- No new metric keys.
- No schema-family fork.
- Existing thresholds and continuity checks remain required.
- Metric cardinality authority remains `metrics` object keys only and must evaluate to `80`
  fail closed.
- v56 closeout must include runtime-observability comparison row against v55 baseline.
- v56 closeout must include metric-key continuity assertion against v55 baseline.
- v56 closeout must include orchestration-state evidence block:
  - block schema is docs-only `v35a_orchestration_state_evidence@1`,
  - schema is docs-defined, but the evidence content must be materialized as a deterministic
    JSON evidence input artifact, included in the canonical closeout path, and treated as
    closeout-authoritative only after implementation,
  - required keys are:
    - `schema`
    - `contract_source`
    - `evidence_input_path`
    - `orchestration_state_snapshot_path`
    - `orchestration_state_snapshot_hash`
    - `execution_topology_state_path`
    - `execution_topology_state_hash`
    - `write_lease_state_path`
    - `write_lease_state_hash`
    - `role_transition_record_path`
    - `role_transition_record_hash`
    - `role_handoff_envelope_path`
    - `role_handoff_envelope_hash`
    - `orchestration_foundation_package`
    - `single_writer_default_enforced`
    - `worker_direct_user_boundary_forbidden`
    - `canonical_identity_fields_recorded`
    - `last_reconciled_event_recorded`
    - `continuation_bridge_ref_recorded`
    - `zero_occurrence_empty_artifacts_materialized`
    - `scope_granularity_enum_frozen`
    - `handoff_reconciliation_required`
    - `verification_passed`
    - `metric_key_cardinality`
    - `metric_key_exact_set_equal_v55`
    - `notes`

## Error/Exit Policy (v56)

- No new stop-gate error-code family is introduced in this arc.
- Existing component-local diagnostics remain authoritative in their respective paths.
- If v56 introduces orchestration-state diagnostics, they must remain deterministic,
  error-only, and fail closed on invalid inputs.
- Deterministic tooling/scripts/tests in this arc use deterministic exit behavior and fail
  closed on invalid inputs.

## Commit / PR Plan (Small Green PRs)

1. `contracts: add v35a orchestration state baseline`
2. `tests: add v35a orchestration evidence and guard suite`

## Intermediate Preconditions (for v56 start)

1. v55 lock implementation and closeout artifacts remain authoritative and unchanged.
2. v55 closeout decision exists and remains green:
   - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS55.md`
3. Existing `V34` closeout artifacts remain available at v56 start:
   - `artifacts/quality_dashboard_v55_closeout.json`
   - `artifacts/stop_gate/metrics_v55_closeout.json`
   - `artifacts/stop_gate/report_v55_closeout.md`
4. Existing `urm_runtime` foundations remain available at v56 start:
   - `packages/urm_runtime/src/urm_runtime/models.py`
   - `packages/urm_runtime/src/urm_runtime/roles.py`
   - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
   - `packages/urm_runtime/src/urm_runtime/storage.py`
   - `packages/urm_runtime/src/urm_runtime/events_tools.py`
   - `packages/urm_runtime/src/urm_runtime/copilot.py`
5. Existing closeout consistency lint remains enabled:
   - `apps/api/scripts/lint_closeout_consistency.py`
6. No additional `L2` boundary release beyond v55 baseline is introduced in this arc.

## Exit Criteria (Draft)

- `A1` and `A2` merged with green CI.
- No new stop-gate metric keys introduced.
- `stop_gate_metrics@1` remains the only stop-gate schema family.
- `V35-A` canonical orchestration-state baseline closes the state-materialization gap
  without widening into worker transcript UX, topology UX, or runtime enforcement.
- v56 closeout evidence includes runtime-observability comparison row against v55 baseline,
  metric-key continuity assertion against v55 baseline, and
  `v35a_orchestration_state_evidence@1`.
- orchestration-state artifacts are deterministic and sufficient to reconstruct role,
  lease, scope, session/event lineage, and compaction linkage.
- zero-occurrence transition/handoff cases materialize deterministic empty artifacts rather
  than omitted state.
- v36-v55 continuity remains green and unreverted.
- no solver semantics contract delta and no trust-lane regression are introduced.
