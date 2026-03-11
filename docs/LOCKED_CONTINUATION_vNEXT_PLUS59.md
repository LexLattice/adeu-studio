# Locked Continuation vNext+59 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS58.md`
- `docs/ASSESSMENT_vNEXT_PLUS58_EDGES.md`
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

- `vNext+58` (`V35-C`, `C1`/`C2`) is merged on `main` with green CI checks.
- `vNext+58` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS58.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS58_EDGES.md` marks the `V35-C` worker transcript/progress
  visibility baseline as closed and restores eligibility for a fresh topology/duty map
  slice.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md` now names `V35-D` as the next default candidate
  after `V35-C` closure.
- current repo reality is narrower than a full topology UX or enforcement lane:
  - `packages/urm_runtime/src/urm_runtime/orchestration_state.py` already emits canonical
    `execution_topology_state@1` and `write_lease_state@1`,
  - `packages/urm_runtime/src/urm_runtime/worker_visibility.py` already emits canonical
    `worker_visibility_state@1`,
  - `packages/urm_runtime/src/urm_runtime/orchestration_evidence.py` already validates
    topology/visibility continuity and fail-closed evidence posture,
  - `apps/api/src/adeu_api/urm_routes.py` already exposes the read-only
    `urm_copilot_visibility_endpoint`,
  - no released canonical `topology_duty_map_state@1` artifact exists on `main`,
  - no released read-only topology/duty map route or equivalent surface exists on `main`,
  - no released topology UX surface projects provenance markers and drilldown refs over the
    canonical topology/visibility/lease substrate,
  - no released `v35d_topology_duty_map_evidence@1` closeout block exists on `main`,
  - no runtime enforcement promotion, multi-writer release, or direct worker/user boundary
    release is present on `main`.
- `vNext+59` therefore selects one thin `V35-D` baseline slice only:
  - read-only topology/duty map observability over the frozen v56/v57/v58 substrate,
  - explicit node/edge provenance markers and provenance-linked inspection refs,
  - explicit current duty, current write-lease holder, and advisory-vs-governance blocker
    rendering,
  - explicit continuation-bridge and compaction-seam visibility where present,
  - canonical closeout evidence integration plus guard coverage,
  - no runtime enforcement promotion, multi-writer release, or direct worker/user
    interaction in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v59,
  - v59 keyset must be exactly equal to v58 keyset,
  - baseline derived cardinality at v59 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v59 is explicit and narrow:
  - this arc authorizes one `L0` topology/duty observability lane only,
  - no `L1` or `L2` authority-surface release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond `main_orchestrator`,
  - no multi-builder or multi-writer release is authorized in this arc.
- `V35-A` state artifacts, `V35-B` delegation/handoff surfaces, and `V35-C` visibility
  surfaces remain frozen prerequisites and are not redefined by this arc.
- The multi-role constitution remains a frozen prerequisite input:
  - `docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json` remains the canonical draft contract
    surface,
  - `docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md` and
    `docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md` remain derived interpretive inputs,
  - this arc may implement the `V35-D` topology/duty map baseline only and may not widen
    the constitutional surface beyond those draft artifacts.
- `V35-D` release-shape lock for v59 is frozen:
  - this arc is a read-only topology/duty map slice only,
  - topology/duty map logic must prefer `packages/urm_runtime` or an explicit new
    read-model surface rather than silent accretion into `packages/adeu_agent_harness`,
  - topology nodes and edges remain observational only in this arc,
  - runtime enforcement and topology-authority promotion remain out of scope for this arc,
  - no direct worker-to-user authority surface is authorized in this arc.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `D1` Canonical topology/duty map read-model baseline (`V35-D`)
2. `D2` Topology/duty map evidence + provenance/guard suite (`V35-D`)

Out-of-scope note:

- runtime enforcement or constitutional promotion in this arc,
- any direct user-to-worker interaction beyond orchestrator mediation in this arc,
- multi-builder or multi-writer execution in this arc,
- treating topology/duty surfaces as accepted truth or governance authority by visibility
  alone,
- closeout hardening bundle (`O1`/`O2`/`O3`) implementation in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v59)

- v60+ `V35-E` runtime enforcement and promotion hardening
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- multi-builder execution, direct worker/user interaction, richer topology UX, and
  stronger authority-surface hardening remain deferred follow-ons under
  `docs/FUTURE_CLEANUPS.md`

## V58 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md",
  "target": "V35-D-baseline",
  "required_continuity_guards": [
    "V35_C_C1_VISIBILITY_STATE_BASELINE_GREEN",
    "V35_C_C2_VISIBILITY_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v58_v35c_visibility_contracts_remain_frozen_while_v35d_topology_and_duty_map_observability_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v59.
- this narrowed machine-checkable consumption block is v58-local only and does not weaken
  the global continuity locks declared above; v36-v58 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V35-D Topology/Duty Map Contract (Machine-Checkable)

```json
{
  "schema": "v35d_topology_duty_map_contract@1",
  "target_arc": "vNext+59",
  "target_path": "V35-D",
  "preserved_authority_inputs": {
    "v35a_state_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1",
    "v35b_delegation_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md#v35b_delegation_handoff_contract@1",
    "v35c_visibility_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md#v35c_transcript_visibility_contract@1",
    "multi_role_contract_baseline": "docs/MULTI_ROLE_EXECUTION_CONTRACTS_v0.json",
    "multi_role_lock_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_LOCK_v0.md",
    "multi_role_policy_baseline": "docs/DRAFT_MULTI_ROLE_EXECUTION_POLICY_v0.md",
    "execution_topology_state_schema": "execution_topology_state@1",
    "write_lease_state_schema": "write_lease_state@1",
    "worker_visibility_state_schema": "worker_visibility_state@1",
    "role_handoff_envelope_schema": "role_handoff_envelope@1",
    "normalized_event_schema": "urm-events@1",
    "copilot_visibility_endpoint": "apps/api/src/adeu_api/urm_routes.py::urm_copilot_visibility_endpoint",
    "v35c_transcript_visibility_evidence": "required_frozen_precondition"
  },
  "topology_map_requirements": {
    "topology_duty_map_state_schema": "topology_duty_map_state@1",
    "topology_duty_map_materializer_required": true,
    "topology_duty_map_foundation_package": "packages/urm_runtime",
    "read_only_topology_required": true,
    "topology_surface_authority_policy": "derived_from_canonical_execution_state_only_non_authoritative_visualization",
    "event_stream_drilldown_policy": "event_streams_are_provenance_targets_only_not_topology_projection_truth_inputs",
    "canonical_input_schemas": [
      "execution_topology_state@1",
      "write_lease_state@1",
      "worker_visibility_state@1",
      "role_handoff_envelope@1"
    ],
    "topology_route_or_equivalent_surface_required": true,
    "required_projection_fields": [
      "orchestrator_session_id",
      "parent_session_id",
      "current_authoritative_holder_actor_id",
      "last_reconciled_event",
      "continuation_bridge_ref",
      "compaction_seams",
      "nodes",
      "edges"
    ],
    "node_required_fields": [
      "actor_id",
      "role",
      "authority_domain",
      "authority_level",
      "current_duty",
      "scope_owned",
      "blocking_state",
      "state_origin",
      "reconciliation_status",
      "last_updated_at",
      "last_reconciled_at",
      "provenance_refs",
      "user_facing_boundary"
    ],
    "edge_required_fields": [
      "source_actor_id",
      "target_actor_id",
      "edge_kind",
      "blocking_state",
      "state_origin",
      "reconciliation_status",
      "last_updated_at",
      "last_reconciled_at",
      "provenance_refs"
    ],
    "write_lease_holder_projection_required": true,
    "support_blockers_advisory_by_default": true,
    "provenance_linkage_required": true,
    "continuation_bridge_and_compaction_visibility_required": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v35d_topology_duty_map_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "topology_duty_map_state_path",
      "topology_duty_map_state_hash",
      "execution_topology_state_path",
      "execution_topology_state_hash",
      "worker_visibility_state_path",
      "worker_visibility_state_hash",
      "derived_from_canonical_execution_state_only",
      "current_write_lease_holder_projected",
      "current_duty_not_authority_inflating",
      "provenance_markers_materialized",
      "artifact_and_event_stream_provenance_refs_resolve",
      "advisory_blockers_not_rendered_as_governance_blockers",
      "continuation_bridge_and_compaction_visibility_preserved",
      "non_authoritative_topology_surface_preserved",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v58",
      "notes"
    ]
  },
  "test_requirements": {
    "topology_duty_map_state_deterministic": true,
    "topology_route_payload_parity_with_topology_duty_map_state": true,
    "write_lease_holder_projection_recorded": true,
    "current_duty_not_authority_inflating": true,
    "node_and_edge_provenance_markers_present": true,
    "provenance_refs_resolve_to_materialized_artifacts_or_event_streams": true,
    "advisory_support_blocker_rendered_as_advisory": true,
    "continuation_bridge_and_compaction_visibility_preserved": true,
    "invented_topology_state_rejected": true,
    "governance_authority_rendering_not_inflated": true,
    "worker_direct_user_boundary_forbidden": true
  },
  "fail_closed_conditions": [
    "topology_duty_map_state_missing",
    "topology_node_or_edge_missing_required_provenance_markers",
    "topology_view_invents_state_not_present_in_canonical_artifacts",
    "current_write_lease_holder_rendered_incorrectly",
    "current_duty_rendered_as_authority_surface",
    "advisory_blocker_rendered_as_governance_equivalent",
    "provenance_ref_missing_or_unresolvable",
    "compaction_or_continuation_bridge_visibility_silently_flattened",
    "topology_surface_treated_as_authoritative",
    "worker_direct_user_boundary_rendered_or_implied"
  ],
  "hash_profile": "sha256_canonical_json_frozen"
}
```

Interpretive notes:

- `execution_topology_state@1` remains the canonical execution-state source; the v59
  topology/duty map is a read-only derived surface over frozen state, visibility, lease,
  and handoff inputs rather than a new authority source.
- `current_duty` is explanatory only in v59. It helps the user inspect what a node is
  doing, but it does not change role authority, lease ownership, or acceptance authority.
- `urm-events@1` may be linked as a drilldown provenance target in v59, but event streams do
  not become topology projection-truth inputs for the derived map.
- support-role blockers remain advisory unless explicitly elevated by `main_orchestrator`;
  topology rendering must not make advisory blockers look governance-equivalent.
- provenance refs must resolve into the committed canonical artifacts or event streams that
  justify the rendered node or edge state.
- compaction seams and continuation bridges must remain explicit where present rather than
  flattening recovered execution history into one undifferentiated graph.

## D1) Canonical Topology/Duty Map Read-Model Baseline (`V35-D`)

### Goal

Make `V35-D` real as a read-only topology/duty map surface over the now-frozen v56/v57/v58
state, delegation, and visibility substrate.

### Scope

- define a deterministic canonical `topology_duty_map_state@1` artifact or equivalent read
  model that projects:
  - orchestrator, builder, and support workers as nodes,
  - delegation and other rendered topology edges,
  - current duty labels and scopes,
  - current authoritative write-lease holder,
  - blocking vs non-blocking state,
  - explicit node and edge provenance markers,
  - provenance-linked inspection refs into canonical artifacts and event streams,
  - continuation-bridge and compaction-seam continuity where present;
- derive the topology/duty map from canonical execution-state, write-lease, visibility, and
  handoff artifacts only;
- allow event streams as drilldown provenance targets only; they must not become projection
  truth inputs for the topology/duty map;
- expose one read-only route or equivalent surface backed by the same canonical payload;
- keep the topology/duty map observational-only and pre-enforcement in this arc.

### Locks

- v59 must not promote topology rendering into runtime authority or governance logic;
- v59 must not invent state not present in canonical artifacts;
- v59 must not release any topology editing, write-lease reassignment, or acceptance action;
- v59 must not imply a direct worker/user interaction surface;
- v59 must not widen into runtime constitutional enforcement.

### Acceptance

- one read-only topology/duty map surface exists and accurately reflects current roles,
  duties, write-lease posture, blocker posture, provenance, and continuity from canonical
  state.

## D2) Topology/Duty Map Evidence + Provenance/Guard Suite (`V35-D`)

### Goal

Make the v59 topology/duty map release closeout-grade rather than UI-only by binding it to
canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v35d_topology_duty_map_evidence@1`;
- validate deterministic topology-duty projection against:
  - `execution_topology_state@1`,
  - `write_lease_state@1`,
  - `worker_visibility_state@1`,
  - `role_handoff_envelope@1`;
- prove node/edge provenance markers and provenance refs are explicit and resolvable;
- fail closed on:
  - invented topology state,
  - incorrect write-lease holder rendering,
  - advisory-blocker authority inflation,
  - continuity flattening,
  - unresolved provenance refs,
  - authoritative topology rendering drift.

### Locks

- the `V35-D` evidence lane must not redefine runtime enforcement semantics;
- v59 closeout evidence must preserve exact stop-gate metric-key continuity versus v58;
- evidence/test wiring must stay pre-enforcement and pre-multi-writer;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v59 closeout can prove that topology/duty rendering is deterministic, provenance-linked,
  observational-only, and continuity-safe without widening into enforcement.

## Implementation Slices

### `D1`

Branch/PR intent:

- add the canonical topology/duty map read model and read-only surface over the v56/v57/v58
  substrate.

Suggested PR title:

- `runtime: add v35d topology duty map baseline`

### `D2`

Branch/PR intent:

- add canonical topology/duty closeout evidence and fail-closed guard coverage.

Suggested PR title:

- `runtime: add v35d topology duty map evidence guards`

## Exit Criteria

`vNext+59` is eligible for closeout only if:

1. `D1` and `D2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `topology_duty_map_state@1` is emitted deterministically.
5. canonical `v35d_topology_duty_map_evidence@1` is emitted and hash-bound.
6. topology/duty rendering remains derived from canonical state only.
7. current write-lease holder, provenance markers, provenance refs, blocker posture, and
   continuity are materially preserved.
8. no runtime enforcement, multi-writer release, or direct worker/user boundary is released
   by this arc.

## Why This Arc, Not `V35-E`

- v58 closed the visibility substrate; v59 can now safely expose the remaining
  non-authoritative topology/duty observability layer on top of frozen state rather than
  jumping straight into runtime enforcement.
- `V35-E` should consume a stable observability surface first so enforcement can target
  proven, inspectable invariants instead of mixing rollout, UX, and enforcement in one arc.
- this keeps the family sequence disciplined:
  - state first (`V35-A`),
  - delegation second (`V35-B`),
  - transcript/progress visibility third (`V35-C`),
  - topology/duty observability fourth (`V35-D`),
  - runtime hardening last (`V35-E`).

## Recommendation

- lock `vNext+59` as a narrow `V35-D` topology/duty map baseline only;
- keep the arc read-only, provenance-linked, and pre-enforcement;
- require topology rendering to stay derived from canonical artifacts and explicit
  continuity markers;
- defer runtime enforcement promotion, multi-writer release, richer topology UX, and direct
  worker/user interaction to later locked work.
