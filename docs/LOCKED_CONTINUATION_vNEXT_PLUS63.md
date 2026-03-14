# Locked Continuation vNext+63 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 14, 2026 UTC).

## Decision Basis

- `vNext+62` (`V36-B`, `B1`/`B2`) is merged on `main` with green CI checks.
- `vNext+62` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md` marks the `V36-B` substrate edge set as closed
  and restores eligibility for the next thin `V36` path.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now names `V36-C` as the next default candidate
  after `V36-B` closure.
- current repo reality is narrower than a diagnostics/compiler lane:
  - canonical `ux_domain_packet@1`, `ux_morph_ir@1`, one accepted bound `V36-A`
    reference pair, the first-family approved profile table, and the same-context
    reachability glossary now exist on `main`,
  - canonical `ux_surface_projection@1`, `ux_interaction_contract@1`, one accepted bound
    `V36-B` reference pair, explicit authority provenance, stable provenance hooks, and
    stable implementation-observable bindings now exist on `main`,
  - no released rendered `artifact_inspector_advisory_workbench` reference surface exists
    on `main`,
  - no released `V36-D` diagnostics/conformance lane or `V36-E` surface-compiler export
    exists on `main`,
  - no released broad `apps/web` retrofit authority or generic design-system release
    exists on `main`.
- `vNext+63` therefore selects one thin `V36-C` baseline slice only:
  - one bounded rendered `artifact_inspector_advisory_workbench` reference surface over
    the released `V36-A` and `V36-B` substrate,
  - explicit epistemic-state rendering, evidence-before-commit preservation, stable
    provenance/binding exposure, and visible advisory/authoritative boundaries,
  - closeout evidence plus determinism/guard coverage,
  - no new diagnostics engine, no conformance-report release, and no compiler widening in
    this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v63,
  - v63 keyset must be exactly equal to v62 keyset,
  - baseline derived cardinality at v63 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v63 is explicit and narrow:
  - this arc authorizes one bounded `L0` rendered reference-surface lane plus its closeout
    evidence lane only,
  - no new `L1` diagnostics/conformance release is authorized in this arc,
  - no `L2` compiler/variant release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35` baseline,
  - no repo-wide route-rewrite authority is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` and `V36-B` substrate surfaces remain frozen prerequisites and are not
  redefined by this arc.
- `V36-C` release-shape lock for v63 is frozen:
  - this arc is one bounded rendered reference-surface baseline only,
  - the arc must consume released `V36-A` and `V36-B` artifacts rather than redefining
    them,
  - the arc must land as one bounded new route or explicitly bounded surface adjacent to
    existing artifact/evidence/copilot terrain rather than as a broad rewrite of
    unrelated routes,
  - the arc must preserve explicit rendering for the frozen epistemic-state vocabulary,
  - the arc must preserve explicit advisory vs authoritative boundaries and an explicit
    commit gate or handoff boundary,
  - the arc must expose the released stable provenance hooks and
    implementation-observable bindings in the rendered surface rather than burying them,
  - the arc may include a diagnostics lane placeholder or artifact-backed read-only lane
    only; no new `V36-D` diagnostics semantics or conformance-report release is
    authorized in this arc,
  - no compiler export, variant widening, generic design-system release, or broad route
    retrofit is authorized in this arc,
  - UI artifacts may express authority but may not mint authority; this arc may not
    weaken any accepted `V35` authority gate by surface arrangement, copy, or salience.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `C1` Artifact inspector / advisory workbench reference surface baseline (`V36-C`)
2. `C2` Rendered reference-surface evidence + determinism/guard suite (`V36-C`)

Out-of-scope note:

- any `V36-D` diagnostics/conformance engine release in this arc,
- any `V36-E` compiler export or lawful variant runtime in this arc,
- any repo-wide design-system, token, or theme overhaul in this arc,
- any broad rewrite of existing `apps/web` routes in this arc,
- any runtime enforcement change in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v63)

- `V36-D` morph diagnostics + conformance baseline
- `V36-E` surface compiler export + controlled variant range
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- the Copilot/Codex CLI approval-flag UX cleanup remains deferred under
  `docs/FUTURE_CLEANUPS.md`

## V62 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md",
  "target": "V36-C-baseline",
  "required_continuity_guards": [
    "V36_B_B1_PROJECTION_INTERACTION_BASELINE_GREEN",
    "V36_B_B2_PROJECTION_INTERACTION_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v62_v36b_projection_and_interaction_substrate_remains_frozen_while_v36c_bounded_rendered_reference_surface_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v63.
- this narrowed machine-checkable consumption block is v62-local only and does not weaken
  the global continuity locks declared above; v14-v62 baseline continuity remains in
  force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V36-C Artifact Inspector Reference Surface Contract (Machine-Checkable)

```json
{
  "schema": "v36c_artifact_inspector_reference_surface_contract@1",
  "target_arc": "vNext+63",
  "target_path": "V36-C",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
    "seed_source_doc": "docs/seed arc v10.md",
    "v36a_domain_morph_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1",
    "v36a_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md",
    "v36b_projection_interaction_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md#v36b_surface_projection_interaction_contract@1",
    "v36b_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md",
    "v35e_runtime_authority_baseline": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
    "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "reference_surface_requirements": {
    "foundation_status": "bounded_rendered_surface_over_released_v36a_v36b_substrate",
    "required_input_artifacts": [
      "ux_domain_packet@1",
      "ux_morph_ir@1",
      "v36a_accepted_reference_instance_pair@1",
      "v36a_first_family_approved_profile_table@1",
      "v36a_same_context_reachability_glossary@1",
      "ux_surface_projection@1",
      "ux_interaction_contract@1",
      "v36b_accepted_reference_pair@1"
    ],
    "rendered_reference_surface_required": true,
    "bounded_route_or_surface_only": true,
    "unrelated_route_rewrite_forbidden": true,
    "reference_surface_family": "artifact_inspector_advisory_workbench",
    "first_reference_profile_id": "artifact_inspector_reference",
    "rendered_surface_must_bind_to_v36b_reference_pair": true,
    "epistemic_state_rendering_required": [
      "loading",
      "draft",
      "candidate",
      "validated",
      "authoritative",
      "conflicted",
      "stale",
      "ambiguous"
    ],
    "rendered_surface_regions_required": [
      "source_artifact_region",
      "candidate_or_proposed_artifact_region",
      "evidence_lane",
      "trust_or_status_lane",
      "advisory_action_lane",
      "explicit_commit_gate_or_handoff_boundary"
    ],
    "diagnostics_lane_mode": "placeholder_or_existing_artifact_backed_only",
    "advisory_authoritative_boundary_rendering_required": true,
    "same_context_reachability_rule_preserved": true,
    "evidence_before_commit_visibility_required": true,
    "required_evidence_reachable_without_route_change_or_commit": true,
    "stable_provenance_hooks_exposed_in_rendered_surface": true,
    "implementation_observable_bindings_exposed_in_rendered_surface": true,
    "minimum_binding_targets": [
      "commit_or_approval_gates",
      "advisory_vs_authoritative_actions",
      "disabled_or_unavailable_gated_states",
      "required_evidence_reachability_anchors",
      "salience_bearing_warning_status_and_diagnostic_surfaces"
    ],
    "runtime_truth_must_remain_derived_from_accepted_artifacts": true,
    "no_event_stream_or_worker_prose_truth_substitution": true,
    "no_visual_authority_inflation": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true,
    "rendered_surface_conformance_hooks_preserved": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v36c_artifact_inspector_reference_surface_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "rendered_surface_route_id",
      "rendered_surface_route_path",
      "rendered_surface_snapshot_path",
      "rendered_surface_snapshot_hash",
      "implementation_binding_manifest_path",
      "implementation_binding_manifest_hash",
      "route_payload_parity_verified",
      "v36b_reference_pair_consumed_without_drift",
      "epistemic_state_rendering_verified",
      "advisory_authoritative_boundary_rendering_verified",
      "same_context_evidence_visibility_preserved",
      "explicit_commit_or_handoff_boundary_visible",
      "stable_provenance_hooks_exposed",
      "implementation_observable_bindings_exposed",
      "no_visual_authority_inflation_preserved",
      "no_unrelated_route_rewrite_detected",
      "no_v36d_diagnostics_engine_widening",
      "no_v36e_compiler_widening",
      "v35_authority_baseline_unchanged",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v62",
      "notes"
    ]
  },
  "test_requirements": {
    "rendered_reference_surface_route_exists": true,
    "route_payload_parity_with_v36b_projection_interaction": true,
    "rendered_surface_snapshot_deterministic": true,
    "implementation_binding_manifest_deterministic": true,
    "epistemic_state_rendering_verified": true,
    "advisory_authoritative_boundary_rendering_verified": true,
    "same_context_evidence_visibility_preserved": true,
    "explicit_commit_or_handoff_boundary_visible": true,
    "stable_provenance_hooks_exposed": true,
    "implementation_observable_bindings_exposed": true,
    "forbidden_authority_inflation_not_rendered": true,
    "no_unrelated_route_rewrite_detected": true,
    "v35_authority_baseline_unchanged": true
  }
}
```

## Why This Arc, Not `V36-D` / `V36-E` or `O1` / `O2` / `O3`

- diagnostics/conformance should not ship before one bounded rendered reference surface
  exists that actually exposes the released bindings, provenance hooks, and epistemic
  distinctions in user-facing form;
- compiler export and lawful variant generation should not ship before one canonical
  rendered surface proves that the released artifact stack compiles into a bounded ADEU
  workbench without authority inflation or evidence-before-commit drift;
- the closeout-hardening bundle remains operational follow-on work and is not a substitute
  for the next thin `V36` reference-surface release.

## Implementation Slices

### `C1` Artifact Inspector / Advisory Workbench Reference Surface Baseline

Required outcome:

- implement one bounded rendered `artifact_inspector_advisory_workbench` reference
  surface over the released `V36-A` and `V36-B` substrate;
- keep the surface adjacent to existing artifact/evidence/copilot terrain while avoiding
  broad route rewrites;
- preserve explicit epistemic-state rendering, evidence-before-commit visibility,
  advisory/authoritative boundaries, and explicit commit or handoff boundaries;
- expose the stable provenance hooks and implementation-observable bindings required for
  later diagnostics and rendered-surface conformance.

Not allowed in `C1`:

- shipping a new diagnostics engine,
- shipping a compiler export or lawful variant system,
- widening into repo-wide redesign or generic theme work,
- relaxing any accepted `V35` authority gate by surface arrangement or copy.

### `C2` Rendered Reference-Surface Evidence + Determinism/Guard Suite

Required outcome:

- emit canonical `v36c_artifact_inspector_reference_surface_evidence@1`,
- prove exact stop-gate key continuity versus v62,
- prove route parity with the released `V36-B` projection/interaction pair,
- prove deterministic rendered-surface snapshot and binding-manifest generation,
- prove explicit epistemic rendering, evidence-before-commit preservation, advisory /
  authoritative boundary preservation, and no unrelated-route rewrite drift.

Not allowed in `C2`:

- diagnostics-engine semantics masquerading as surface evidence,
- compiler-export semantics masquerading as route evidence,
- metric-key expansion or schema-family forks.

## Exit Criteria

`vNext+63` is complete only if:

1. `C1` and `C2` merge with green CI.
2. One bounded rendered `artifact_inspector_advisory_workbench` reference surface exists
   on `main` and is traceable back to the released `V36-A` / `V36-B` artifacts.
3. Canonical `v36c_artifact_inspector_reference_surface_evidence@1` exists on `main`.
4. Exact stop-gate metric-key equality with v62 is preserved and derived cardinality
   remains `80`.
5. No diagnostics-engine, compiler-export, or broad route-retrofit widening is released.
