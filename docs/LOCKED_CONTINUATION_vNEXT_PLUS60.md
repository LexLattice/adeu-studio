# Locked Continuation vNext+60 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS59.md`
- `docs/ASSESSMENT_vNEXT_PLUS59_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md`
- `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 12, 2026 UTC).

## Decision Basis

- `vNext+59` (`V35-D`, `D1`/`D2`) is merged on `main` with green CI checks.
- `vNext+59` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS59.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS59_EDGES.md` marks the `V35-D` topology/duty-map baseline as
  closed and restores eligibility for a fresh runtime-enforcement slice.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md` now names `V35-E` as the next default candidate
  after `V35-D` closure.
- current repo reality is narrower than a full constitutional runtime lane:
  - `packages/urm_runtime/src/urm_runtime/orchestration_state.py`,
    `worker_visibility.py`, and `topology_duty_map.py` already emit the canonical state,
    visibility, and topology substrates that enforcement should consume,
  - `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py` already proves the
    major v35a-v35d invariants post-hoc at closeout,
  - `apps/api/src/adeu_api/urm_routes.py` already routes spawn/mode/tool actions through
    `authorize_action(...)`,
  - `packages/urm_runtime/src/urm_runtime/copilot.py` already enforces the released child
    delegation role surface, `granted_role == requested_role`, and
    `write_task -> builder_worker` coupling,
  - no released bounded `V35-E` runtime-enforcement bundle exists on `main`,
  - no released canonical `v35e_runtime_enforcement_evidence@1` closeout block exists on
    `main`,
  - no automatic acceptance, no automatic closeout, no multi-writer release, and no direct
    worker/user boundary release is present on `main`.
- `vNext+60` therefore selects one thin `V35-E` baseline slice only:
  - bounded runtime enforcement over the frozen v56/v57/v58/v59 substrate,
  - deterministic denial surfaces for a narrow set of constitutional violations at
    existing orchestration boundaries,
  - closeout evidence integration plus guard coverage,
  - no multi-writer release, direct worker/user interaction, or closeout-automation
    widening in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v60,
  - v60 keyset must be exactly equal to v59 keyset,
  - baseline derived cardinality at v60 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v60 is explicit and narrow:
  - this arc authorizes one `L1` runtime-enforcement lane only,
  - no `L2` authority-surface release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond `main_orchestrator`,
  - no multi-builder or multi-writer release is authorized in this arc.
- `V35-A` state artifacts, `V35-B` delegation/handoff surfaces, `V35-C` visibility
  surfaces, and `V35-D` topology surfaces remain frozen prerequisites and are not
  redefined by this arc.
- The multi-role constitution remains a frozen prerequisite input:
  - `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json` remains the canonical draft contract
    surface,
  - `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md` and
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md` remain derived interpretive inputs,
  - this arc may implement the `V35-E` bounded runtime-enforcement baseline only and may
    not widen the constitutional surface beyond those draft artifacts.
- `V35-E` release-shape lock for v60 is frozen:
  - this arc is a bounded runtime-enforcement slice only,
  - enforcement logic must prefer `packages/urm_runtime` or an explicit new orchestration
    surface rather than silent accretion into `packages/adeu_agent_harness`,
  - enforcement must consume the released read-only state/visibility/topology surfaces
    rather than redefining them,
  - automatic acceptance and automatic closeout remain out of scope for this arc,
  - topology and visibility surfaces remain observational-only in this arc,
  - no topology editing, write-lease reassignment, multi-writer release, or direct
    worker-to-user authority surface is authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `E1` Bounded runtime-enforcement baseline (`V35-E`)
2. `E2` Runtime-enforcement evidence + denial/guard suite (`V35-E`)

Out-of-scope note:

- any automatic acceptance or automatic closeout in this arc,
- any direct user-to-worker interaction beyond orchestrator mediation in this arc,
- any multi-builder or multi-writer execution in this arc,
- any topology or visibility redesign beyond what v58/v59 already released,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v60)

- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- multi-builder execution, multi-writer execution, direct worker/user interaction, richer
  UX shaping, and broader authority-surface hardening remain deferred follow-ons under
  `docs/FUTURE_CLEANUPS.md`

## V59 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md",
  "target": "V35-E-baseline",
  "required_continuity_guards": [
    "V35_D_D1_TOPOLOGY_DUTY_MAP_BASELINE_GREEN",
    "V35_D_D2_TOPOLOGY_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v59_v35d_topology_contracts_remain_frozen_while_v35e_bounded_runtime_enforcement_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v60.
- this narrowed machine-checkable consumption block is v59-local only and does not weaken
  the global continuity locks declared above; v36-v59 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V35-E Runtime Enforcement Contract (Machine-Checkable)

```json
{
  "schema": "v35e_runtime_enforcement_contract@1",
  "target_arc": "vNext+60",
  "target_path": "V35-E",
  "preserved_authority_inputs": {
    "v35a_state_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1",
    "v35b_delegation_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md#v35b_delegation_handoff_contract@1",
    "v35c_visibility_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md#v35c_transcript_visibility_contract@1",
    "v35d_topology_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md#v35d_topology_duty_map_contract@1",
    "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
    "multi_role_lock_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md",
    "multi_role_policy_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md",
    "execution_topology_state_schema": "execution_topology_state@1",
    "write_lease_state_schema": "write_lease_state@1",
    "role_transition_record_schema": "role_transition_record@1",
    "role_handoff_envelope_schema": "role_handoff_envelope@1",
    "worker_visibility_state_schema": "worker_visibility_state@1",
    "topology_duty_map_state_schema": "topology_duty_map_state@1",
    "normalized_event_schema": "urm-events@1",
    "spawn_authorization_entrypoint": "packages/urm_runtime/src/urm_runtime/capability_policy.py::authorize_action",
    "copilot_spawn_endpoint": "apps/api/src/adeu_api/urm_routes.py::urm_agent_spawn_endpoint",
    "v35d_topology_evidence": "required_frozen_precondition"
  },
  "runtime_enforcement_requirements": {
    "runtime_enforcement_foundation_package": "packages/urm_runtime",
    "deterministic_denial_policy": "error_only_fail_closed_with_stable_urm_error_codes",
    "observability_surfaces_remain_read_only": true,
    "acceptance_and_closeout_authority_preserved": true,
    "worker_direct_user_boundary_forbidden": true,
    "claimed_work_presence_fields": [
      "files_changed",
      "commands_run",
      "artifacts_produced",
      "evidence_refs"
    ],
    "canonical_input_schemas": [
      "execution_topology_state@1",
      "write_lease_state@1",
      "role_transition_record@1",
      "role_handoff_envelope@1",
      "worker_visibility_state@1",
      "topology_duty_map_state@1"
    ],
    "required_enforcement_surfaces": [
      "spawn_request_boundary",
      "orchestration_state_materialization_boundary",
      "worker_visibility_materialization_boundary",
      "topology_duty_map_materialization_boundary"
    ],
    "required_enforced_invariants": [
      "granted_role_equals_requested_role_for_released_child_roles",
      "write_task_requires_builder_worker",
      "single_builder_default_runtime_enforced",
      "support_roles_non_authoritative_runtime_enforced",
      "support_role_proxy_write_authority_blocked",
      "scope_granularity_kind_present_and_valid",
      "claimed_work_handoff_required_fields_enforced",
      "acceptance_and_closeout_authority_preserved",
      "worker_direct_user_boundary_forbidden"
    ]
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v35e_runtime_enforcement_evidence@1",
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
      "worker_visibility_state_path",
      "worker_visibility_state_hash",
      "topology_duty_map_state_path",
      "topology_duty_map_state_hash",
      "spawn_boundary_enforcement_active",
      "single_builder_default_enforced_at_runtime",
      "support_role_proxy_authority_blocked",
      "claimed_work_handoff_validation_enforced",
      "scope_kind_validation_enforced",
      "deterministic_denial_surfaces_recorded",
      "observability_surfaces_remain_read_only",
      "acceptance_and_closeout_authority_preserved",
      "worker_direct_user_boundary_forbidden",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v59",
      "notes"
    ]
  },
  "test_requirements": {
    "runtime_enforcement_denies_invalid_spawn_role_task_combinations": true,
    "runtime_enforcement_denies_single_builder_default_violations": true,
    "runtime_enforcement_denies_support_role_proxy_authority": true,
    "runtime_enforcement_denies_claimed_work_handoff_missing_required_fields": true,
    "runtime_enforcement_denies_invalid_scope_kind": true,
    "deterministic_denial_codes_recorded": true,
    "observability_surfaces_remain_read_only": true,
    "acceptance_and_closeout_authority_preserved": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "fail_closed_conditions": [
    "runtime_enforcement_surface_missing",
    "invalid_spawn_role_task_combination_accepted",
    "single_builder_default_violation_accepted",
    "support_role_proxy_authority_violation_accepted",
    "claimed_work_handoff_missing_required_fields_accepted",
    "scope_kind_missing_or_malformed_accepted",
    "observability_surface_promoted_to_authority",
    "acceptance_or_closeout_authority_released",
    "worker_direct_user_boundary_rendered_or_permitted",
    "deterministic_denial_code_missing_or_unstable"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

Interpretive notes:

- v60 consumes the released v35a-v35d state, delegation, visibility, and topology surfaces
  as truth inputs; enforcement adds bounded denial logic and must not become a new truth
  source by itself.
- topology and visibility routes remain observational-only in v60 even when enforcement is
  added elsewhere; enforcement must not silently promote those read surfaces into accepted
  authority.
- "claimed work present" means any non-empty `files_changed`, `commands_run`,
  `artifacts_produced`, or `evidence_refs` surface in a completed worker handoff entry.
- support-role proxy authority means a non-builder delegated role attempting to gain or
  imply authoritative write ownership, implementation acceptance, or equivalent proxy
  authority through task kind, scope, or artifact-execution posture.
- deterministic denial codes must stay error-only and stable enough for tests, replay, and
  closeout evidence to bind the released enforcement behavior.

## E1) Bounded Runtime-Enforcement Baseline (`V35-E`)

### Goal

Make `V35-E` real as a bounded runtime-enforcement lane over the now-frozen v56/v57/v58/v59
observability substrate.

### Scope

- promote a narrow set of existing constitutional invariants into runtime denials at
  already-released orchestration boundaries;
- enforce spawn-boundary role/task/scope/lease coherence against the released child-role
  surface and single-builder default;
- reject support-role proxy authority attempts that would imply builder-only write posture
  or implementation authority;
- enforce scope-kind presence and validity against the frozen scope-granularity surface;
- enforce claimed-work handoff required fields when canonical handoff materialization
  encounters completed delegated work that claims outputs;
- surface deterministic fail-closed error codes and context for the frozen denied cases;
- keep topology and visibility read surfaces observational-only and keep acceptance and
  closeout authority in ADEU.

### Locks

- v60 must not widen runtime enforcement beyond the currently frozen constitutional
  surface;
- v60 must not release automatic acceptance, automatic closeout, or multi-writer behavior;
- v60 must not redefine topology or visibility truth surfaces;
- v60 must not imply a direct worker/user interaction surface;
- v60 must not widen into the separate closeout-hardening bundle.

### Acceptance

- one bounded runtime-enforcement lane exists and rejects the frozen invalid cases
  deterministically while preserving the already-released happy path and authority
  boundaries.

## E2) Runtime-Enforcement Evidence + Denial/Guard Suite (`V35-E`)

### Goal

Make the v60 runtime-enforcement release closeout-grade rather than relying on code paths
alone by binding it to canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v35e_runtime_enforcement_evidence@1`;
- validate enforcement outcomes and preserved authority posture against:
  - `orchestration_state_snapshot@1`,
  - `write_lease_state@1`,
  - `role_transition_record@1`,
  - `role_handoff_envelope@1`,
  - `worker_visibility_state@1`,
  - `topology_duty_map_state@1`;
- prove deterministic denial surfaces are explicit and stable for the frozen invalid cases;
- fail closed on:
  - invalid role/task/scope combinations being accepted,
  - single-builder default violations being accepted,
  - support-role proxy authority being accepted,
  - claimed-work handoff required-field gaps being accepted,
  - observability-surface authority inflation,
  - acceptance/closeout authority drift,
  - worker direct user-boundary drift.

### Locks

- the `V35-E` evidence lane must not redefine semantics or widen authority surfaces;
- v60 closeout evidence must preserve exact stop-gate metric-key continuity versus v59;
- evidence/test wiring must stay pre-multi-writer and pre-closeout-automation;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v60 closeout can prove that bounded runtime enforcement is active, deterministic,
  fail-closed, and authority-preserving without widening into multi-writer or
  closeout-automation work.

## Implementation Slices

### `E1`

Branch/PR intent:

- add the bounded runtime-enforcement baseline over the released v56-v59 substrate.

Suggested PR title:

- `runtime: add v60 e1 bounded runtime enforcement`

### `E2`

Branch/PR intent:

- add canonical v60 enforcement closeout evidence and fail-closed denial/guard coverage.

Suggested PR title:

- `runtime: add v60 e2 enforcement evidence guards`

## Exit Criteria

`vNext+60` is eligible for closeout only if:

1. `E1` and `E2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `v35e_runtime_enforcement_evidence@1` is emitted and hash-bound.
5. bounded runtime enforcement denies the frozen invalid role/task/scope/authority cases
   deterministically.
6. observability surfaces remain read-only and non-authoritative.
7. acceptance and closeout authority remain with ADEU / `main_orchestrator`.
8. no multi-writer release, no direct worker/user boundary, and no closeout automation are
   released by this arc.

## Why This Arc, Not `O1` / `O2` / `O3`

- `V35-E` is the last remaining locked path in the v9 family, and it depends directly on
  the stable v56-v59 state/visibility/topology substrate that now exists on `main`.
- the closeout-hardening bundle is operationally useful but orthogonal; it should not
  replace the still-unreleased bounded enforcement path inside the v35 family.
- keeping v60 focused on bounded runtime enforcement preserves the established sequence:
  - state first (`V35-A`),
  - delegation second (`V35-B`),
  - transcript/progress visibility third (`V35-C`),
  - topology/duty observability fourth (`V35-D`),
  - bounded runtime hardening fifth (`V35-E`).

## Recommendation

- lock `vNext+60` as a narrow `V35-E` bounded runtime-enforcement baseline only;
- keep the arc authority-preserving, deterministic, and fail-closed;
- require enforcement to consume the already-released state/visibility/topology surfaces
  rather than redefining them;
- defer closeout hardening, multi-writer release, richer UX, and direct worker/user
  interaction to later locked work.
