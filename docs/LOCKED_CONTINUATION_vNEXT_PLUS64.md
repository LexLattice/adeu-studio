# Locked Continuation vNext+64 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
- `docs/ASSESSMENT_vNEXT_PLUS63_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 15, 2026 UTC).

## Decision Basis

- `vNext+63` (`V36-C`, `C1`/`C2`) is merged on `main` with green CI checks.
- `vNext+63` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS63_EDGES.md` marks the `V36-C` rendered reference-surface
  edge set as closed and restores eligibility for the next thin `V36` path.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now names `V36-D` as the next default candidate
  after `V36-C` closure.
- current repo reality is narrower than a compiler/variant lane:
  - canonical `ux_domain_packet@1`, `ux_morph_ir@1`, one accepted bound `V36-A`
    reference pair, the first-family approved profile table, and the same-context
    reachability glossary exist on `main`,
  - canonical `ux_surface_projection@1`, `ux_interaction_contract@1`, one accepted bound
    `V36-B` reference pair, explicit authority provenance, stable provenance hooks, and
    stable implementation-observable bindings exist on `main`,
  - one bounded rendered `artifact_inspector_advisory_workbench` route, one rendered
    route contract, one semantic snapshot, one implementation binding manifest, and
    canonical `v36c_artifact_inspector_reference_surface_evidence@1` now exist on
    `main`,
  - no released `ux_morph_diagnostics@1` artifact family exists on `main`,
  - no released `ux_conformance_report@1` artifact family exists on `main`,
  - no released `V36-E` compiler export or lawful variant runtime exists on `main`.
- `vNext+64` therefore selects one thin `V36-D` baseline slice only:
  - canonical deterministic diagnostics for the bounded
    `artifact_inspector_advisory_workbench` family over the released `V36-A` / `V36-B` /
    `V36-C` substrate,
  - a minimal typed conformance bridge over those diagnostics for the same bounded family,
  - closeout evidence plus determinism/guard coverage,
  - no compiler export, no lawful variant widening, no runtime auto-repair, and no broad
    route rewrite in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v64,
  - v64 keyset must be exactly equal to v63 keyset,
  - baseline derived cardinality at v64 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v64 is explicit and narrow:
  - this arc authorizes one bounded `L1` diagnostics/conformance substrate lane plus its
    closeout evidence lane only,
  - no `L2` compiler/variant release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35` baseline,
  - no repo-wide route-rewrite authority is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A`, `V36-B`, and `V36-C` surfaces remain frozen prerequisites and are not
  redefined by this arc.
- `V36-D` release-shape lock for v64 is frozen:
  - this arc is one bounded morph-diagnostics and conformance baseline only,
  - the arc must consume released `V36-A`, `V36-B`, and `V36-C` artifacts rather than
    redefining them,
  - the diagnostics and conformance artifacts must remain bound to the same
    `reference_surface_family`, `reference_instance_id`, and `approved_profile_id` as
    the accepted `V36-A` pair, accepted `V36-B` pair, and released `V36-C` route,
  - diagnostics must remain constitutional/audit artifacts first, not aesthetic taste
    engines,
  - diagnostics must trace to the canonical domain/morph/projection/interaction/rendered
    artifact stack rather than free-form critique,
  - conformance, if emitted, must remain a typed summary derived from canonical
    diagnostics plus frozen rendered-surface assertion inputs rather than prose judgment
    or runtime auto-repair,
  - no compiler export, lawful variant widening, generic design-system release, or broad
    route retrofit is authorized in this arc,
  - UI artifacts may express authority but may not mint authority; this arc may not
    weaken any accepted `V35` authority gate by diagnostic wording, conformance wording,
    or salience.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `D1` Morph diagnostics + conformance baseline (`V36-D`)
2. `D2` Morph diagnostics/conformance evidence + determinism/guard suite (`V36-D`)

Out-of-scope note:

- any `V36-E` compiler export or lawful variant release in this arc,
- any broad rewrite of existing `apps/web` routes in this arc,
- any repo-wide design-system, token, or theme overhaul in this arc,
- any runtime enforcement or runtime auto-repair change in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v64)

- `V36-E` surface compiler export + controlled variant range
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- the Copilot/Codex CLI approval-flag UX cleanup remains deferred under
  `docs/FUTURE_CLEANUPS.md`

## V63 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md",
  "target": "V36-D-baseline",
  "required_continuity_guards": [
    "V36_C_C1_RENDERED_REFERENCE_SURFACE_BASELINE_GREEN",
    "V36_C_C2_RENDERED_REFERENCE_SURFACE_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v63_v36c_rendered_reference_surface_remains_frozen_while_v36d_bounded_morph_diagnostics_and_conformance_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v64.
- this narrowed machine-checkable consumption block is v63-local only and does not weaken
  the global continuity locks declared above; v14-v63 baseline continuity remains in
  force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V36-D Morph Diagnostics / Conformance Contract (Machine-Checkable)

```json
{
  "schema": "v36d_morph_diagnostics_conformance_contract@1",
  "target_arc": "vNext+64",
  "target_path": "V36-D",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
    "seed_source_doc": "docs/seed arc v10.md",
    "v36a_domain_morph_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1",
    "v36a_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md",
    "v36b_projection_interaction_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md#v36b_surface_projection_interaction_contract@1",
    "v36b_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md",
    "v36c_rendered_reference_surface_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md#v36c_artifact_inspector_reference_surface_contract@1",
    "v36c_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md",
    "v35e_runtime_authority_baseline": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
    "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "diagnostics_conformance_requirements": {
    "foundation_status": "deterministic_diagnostics_and_conformance_over_released_v36a_v36b_v36c_substrate",
    "required_input_artifacts": [
      "ux_domain_packet@1",
      "ux_morph_ir@1",
      "v36a_accepted_reference_instance_pair@1",
      "v36a_first_family_approved_profile_table@1",
      "v36a_same_context_reachability_glossary@1",
      "ux_surface_projection@1",
      "ux_interaction_contract@1",
      "v36b_accepted_reference_pair@1",
      "v36c_rendered_reference_surface_contract@1",
      "v36c_rendered_reference_surface_semantic_snapshot@1",
      "v36c_rendered_reference_surface_binding_manifest@1",
      "v36c_artifact_inspector_reference_surface_evidence@1"
    ],
    "reference_surface_family": "artifact_inspector_advisory_workbench",
    "required_reference_binding_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id"
    ],
    "first_reference_profile_id": "artifact_inspector_reference",
    "first_reference_profile_must_exist_in_v36a_approved_profile_table": true,
    "ux_morph_diagnostics_schema_required": true,
    "ux_conformance_report_schema_required": true,
    "diagnostics_severity_taxonomy": [
      "error",
      "warning",
      "advisory"
    ],
    "diagnostics_must_trace_to_canonical_artifact_stack": true,
    "diagnostics_provenance_pointers_required": true,
    "rendered_surface_assertion_bridge_required": true,
    "rendered_surface_assertion_inputs": [
      "v36c_rendered_reference_surface_contract@1",
      "v36c_rendered_reference_surface_semantic_snapshot@1",
      "v36c_rendered_reference_surface_binding_manifest@1"
    ],
    "conformance_report_must_be_typed_and_diagnostics_derived": true,
    "conformance_overall_judgment_enum": [
      "pass",
      "fail",
      "needs_review"
    ],
    "seeded_first_family_violation_families": [
      "destructive_action_lacks_adequate_confirmation",
      "provisional_data_rendered_with_authoritative_styling",
      "required_evidence_not_reachable_within_same_bounded_workbench_context",
      "utility_target_conflicts_with_density_or_information_posture",
      "requested_interaction_profile_conflicts_with_realized_command_grammar",
      "competing_primary_actions_in_one_region",
      "failure_mode_lacks_visible_recovery_path",
      "advisory_authoritative_boundary_visually_collapsed"
    ],
    "event_streams_and_worker_prose_provenance_only": true,
    "no_aesthetic_taste_engine": true,
    "no_runtime_auto_repair_or_self_mutating_ui": true,
    "no_visual_authority_inflation": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v36d_morph_diagnostics_conformance_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "ux_morph_diagnostics_schema_path",
      "ux_morph_diagnostics_schema_hash",
      "ux_conformance_report_schema_path",
      "ux_conformance_report_schema_hash",
      "ux_morph_diagnostics_reference_path",
      "ux_morph_diagnostics_reference_hash",
      "ux_conformance_report_reference_path",
      "ux_conformance_report_reference_hash",
      "v36a_reference_pair_consumed_without_drift",
      "v36b_reference_pair_consumed_without_drift",
      "v36c_rendered_surface_consumed_without_drift",
      "reference_profile_id_verified_against_v36a_table",
      "diagnostics_severity_taxonomy_verified",
      "seeded_violation_detection_verified",
      "diagnostics_provenance_pointer_resolution_verified",
      "rendered_surface_assertion_bridge_verified",
      "conformance_report_diagnostics_derivation_verified",
      "same_context_reachability_violation_detectable",
      "provisional_authoritative_styling_violation_detectable",
      "advisory_authoritative_boundary_collapse_detectable",
      "recovery_path_gap_detectable",
      "no_taste_engine_drift_detected",
      "no_event_stream_or_worker_prose_truth_substitution",
      "v35_authority_baseline_unchanged",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v63",
      "notes"
    ]
  },
  "test_requirements": {
    "ux_morph_diagnostics_schema_serialization_deterministic": true,
    "ux_conformance_report_schema_serialization_deterministic": true,
    "reference_diagnostics_serialization_deterministic": true,
    "reference_conformance_report_serialization_deterministic": true,
    "v36a_reference_pair_consumed_without_drift": true,
    "v36b_reference_pair_consumed_without_drift": true,
    "v36c_rendered_surface_consumed_without_drift": true,
    "reference_profile_id_verified_against_v36a_table": true,
    "diagnostics_severity_taxonomy_verified": true,
    "seeded_violation_detection_verified": true,
    "diagnostics_provenance_pointer_resolution_verified": true,
    "rendered_surface_assertion_bridge_verified": true,
    "conformance_report_diagnostics_derivation_verified": true,
    "same_context_reachability_violation_detectable": true,
    "provisional_authoritative_styling_violation_detectable": true,
    "advisory_authoritative_boundary_collapse_detectable": true,
    "recovery_path_gap_detectable": true,
    "no_taste_engine_drift_detected": true,
    "no_event_stream_or_worker_prose_truth_substitution": true,
    "v35_authority_baseline_unchanged": true
  }
}
```

Interpretive notes:

- v64 defines diagnostics and conformance artifacts only; it does not yet authorize a
  compiler export, lawful variant runtime, or runtime auto-repair behavior.
- diagnostics must remain artifact-backed constitutional findings, not a prose review lane
  or aesthetic preference engine.
- conformance exists in v64 only as a typed summary over canonical diagnostics plus frozen
  rendered-surface assertion inputs; it must not collapse into UI-local heuristics or
  runtime policy minting.
- event streams and worker prose may appear as provenance aids only; they do not become
  accepted truth or diagnostic truth by being present in a rendered route or a diagnostic
  artifact.

## D1) Canonical Morph Diagnostics + Conformance Baseline (`V36-D`)

### Goal

Make `V36-D` real as a deterministic diagnostics/conformance substrate rather than manual
UX-law review.

### Scope

- add canonical `ux_morph_diagnostics@1` and canonical `ux_conformance_report@1` schemas
  for the bounded `artifact_inspector_advisory_workbench` family;
- add one accepted deterministic reference diagnostics artifact and one accepted
  deterministic conformance report, bound by the shared
  `reference_surface_family`, `reference_instance_id`, and `approved_profile_id` fields
  back to the released `V36-A`, `V36-B`, and `V36-C` substrate;
- freeze the minimum severity taxonomy:
  `error`, `warning`, `advisory`;
- freeze provenance pointers from diagnostics into the canonical
  domain/morph/projection/interaction/rendered artifact stack;
- freeze the rendered-surface assertion bridge over the released v63 route contract,
  semantic snapshot, and implementation binding manifest;
- freeze deterministic seeded detection coverage for the first-family violation set:
  confirmation gaps, provisional/authoritative styling drift, same-context evidence
  reachability violations, utility/posture conflicts, command-grammar conflicts,
  competing primaries, missing recovery paths, and advisory/authoritative collapse;
- keep conformance typed and diagnostics-derived rather than prose-like or heuristic-first.

### Locks

- v64 must not widen into compiler export, lawful variant generation, or broad route
  rewrites;
- v64 must not redefine the released `V36-A`, `V36-B`, or `V36-C` artifacts;
- v64 must not widen into runtime auto-repair or self-mutating UI behavior;
- diagnostics/conformance wording must not mint new authority, weaken gates, or
  reinterpret accepted runtime truth;
- v64 must not widen into the separate closeout-hardening bundle.

### Acceptance

- one bounded typed diagnostics/conformance layer exists on `main` with canonical
  schemas, one coherent accepted reference diagnostics artifact, one coherent accepted
  conformance report, frozen severity taxonomy, deterministic seeded violation coverage,
  provenance into the canonical artifact stack, and a rendered-surface assertion bridge,
  all serializable and hashable deterministically without authority drift.

## D2) Diagnostics/Conformance Evidence + Determinism/Guard Suite (`V36-D`)

### Goal

Make the v64 `V36-D` release closeout-grade rather than relying on schema files alone by
binding it to canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v36d_morph_diagnostics_conformance_evidence@1`;
- validate schema/reference outputs against the frozen `V36-D` contract and consumed
  `V36-A` / `V36-B` / `V36-C` substrate;
- prove deterministic serialization and hash binding for the canonical artifacts;
- fail closed on:
  - missing accepted diagnostics artifact or conformance report,
  - diagnostics/conformance binding mismatch against the released substrate,
  - invalid or missing severity taxonomy entries,
  - missing provenance pointers into the canonical artifact stack,
  - missing rendered-surface assertion bridge against the v63 route contract, semantic
    snapshot, or implementation binding manifest,
  - failure to surface seeded first-family violations deterministically,
  - prose-like or taste-engine diagnostic drift,
  - event-stream or worker-prose truth substitution,
  - authority-minting drift in diagnostics/conformance wording,
  - stop-gate metric-key continuity drift.

### Locks

- the `V36-D` evidence lane must not redefine semantics or widen authority surfaces;
- v64 closeout evidence must preserve exact stop-gate metric-key continuity versus v63;
- evidence/test wiring must stay pre-compiler and pre-variant;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v64 closeout can prove that the `V36-D` diagnostics/conformance layer is canonical,
  deterministic, fail-closed, and authority-preserving without widening into compiler
  export, variant runtime, or route rewrites;
- v64 closeout can prove that the accepted diagnostics/conformance artifacts remain
  anchored to the released accepted `V36-A` / `V36-B` / `V36-C` substrate, preserve
  seeded violation detection with canonical provenance, and keep conformance derived from
  typed diagnostics rather than prose heuristics.

## Implementation Slices

### `D1`

Branch/PR intent:

- add the canonical morph diagnostics and conformance baseline for the first bounded
  surface family.

Suggested PR title:

- `ux: add v64 d1 morph diagnostics baseline`

### `D2`

Branch/PR intent:

- add canonical v64 diagnostics/conformance closeout evidence and fail-closed guard
  coverage.

Suggested PR title:

- `ux: add v64 d2 diagnostics conformance evidence guards`

## Exit Criteria

`vNext+64` is eligible for closeout only if:

1. `D1` and `D2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `ux_morph_diagnostics@1`, canonical `ux_conformance_report@1`, and
   canonical `v36d_morph_diagnostics_conformance_evidence@1` exist on `main`.
5. accepted diagnostics/conformance artifacts serialize deterministically and remain
   coherently bound to the released accepted `V36-A`, `V36-B`, and `V36-C` substrate.
6. seeded first-family violations are surfaced deterministically with the frozen
   severity taxonomy and provenance pointers into the canonical artifact stack.
7. the rendered-surface assertion bridge remains frozen over the v63 route contract,
   semantic snapshot, and implementation binding manifest.
8. diagnostics/conformance remain constitutional and typed:
   no taste-engine drift, no event/prose truth substitution, and no authority-minting
   wording drift.
9. no compiler-export widening, lawful variant widening, runtime auto-repair, or broad
   route-retrofit release is shipped by this arc.

## Why This Arc, Not `V36-E` or `O1` / `O2` / `O3`

- compiler export and lawful variant generation should not ship before deterministic
  diagnostics/conformance exists over the first bounded rendered reference surface;
- the closed v63 route already exposes the bindings, provenance hooks, and semantic
  snapshot needed for diagnostics, so v64 is the structurally correct point to freeze the
  audit lane rather than widening directly into compiler behavior;
- the closeout-hardening bundle remains operationally useful but orthogonal; it should
  not replace the next unreleased path inside the `V36` family.

## Recommendation

- lock `vNext+64` as a narrow `V36-D` diagnostics/conformance baseline only;
- keep the arc artifact-first, deterministic, and authority-preserving;
- require canonical diagnostics/conformance schemas, accepted reference artifacts,
  canonical provenance, and rendered-surface assertion bridging before any compiler or
  lawful variant work;
- defer compiler export, variant widening, and the separate closeout-hardening track to
  later locked arcs.
