# Locked Continuation vNext+131

Status: `V44-A` implementation contract.

## V131 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v44a_structural_reasoning_probe_trace_contract@1",
  "target_arc": "vNext+131",
  "target_path": "V44-A",
  "target_scope": "bounded_repo_owned_reasoning_template_probe_and_structural_trace_contracts_prior_to_taxonomy_profile_or_benchmark_scoring",
  "implementation_packages": [
    "adeu_reasoning_assessment"
  ],
  "governing_released_stack": "V41_practical_analysis_plus_V42_local_contest_specialization_on_main",
  "governing_stack_consumption_mode": "released_v41_v42_lessons_only_no_v43_contest_doctrine_no_v46_benchmark_scoring_or_promotion",
  "source_intake_bundle": "examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "selected_schema_ids": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1"
  ],
  "selected_owner_surface": "packages/adeu_reasoning_assessment",
  "selected_template_class_vocabulary": [
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation"
  ],
  "hierarchical_probe_posture_required": true,
  "hierarchical_probe_shape_selected": "parent_child_active_step_with_explicit_top_level_plan_spine_and_return_posture",
  "hierarchical_depth_selected": "single_level_parent_child_only",
  "lane_vocabulary_frozen": [
    "O",
    "E",
    "D",
    "U"
  ],
  "trace_event_vocabulary_frozen": [
    "step_activate",
    "step_complete",
    "branch_select",
    "blocked",
    "invalid_early_closure",
    "repair_enter",
    "repair_exit",
    "return_to_parent"
  ],
  "terminal_trace_status_vocabulary_frozen": [
    "completed_clean",
    "completed_with_structural_break",
    "blocked",
    "invalid_early_closure"
  ],
  "paired_condition_compatibility_fields_required": true,
  "paired_condition_compatibility_mode": "minimal_reference_posture_only_no_embedded_benchmark_instance_machinery",
  "structural_break_evidence_required": true,
  "score_fields_forbidden_in_v44a": true,
  "profile_fields_forbidden_in_v44a": true,
  "taxonomy_release_forbidden_in_v44a": true,
  "benchmark_projection_consumer_only_deferred_to_v46": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v131_closeout.json",
    "artifacts/stop_gate/metrics_v131_closeout.json",
    "artifacts/stop_gate/report_v131_closeout.md"
  ]
}
```

## Objective

Release the bounded `V44-A` starter seam by defining one repo-owned template-probe
contract and one repo-owned structural-trace contract under
`packages/adeu_reasoning_assessment`, with explicit support for both flat and
hierarchical probe structure but no taxonomy, no model-profile aggregation, and no
benchmark scoring or promotion.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_reasoning_assessment`
- one probe artifact contract only:
  - `adeu_reasoning_template_probe@1`
- one trace artifact contract only:
  - `adeu_structural_reasoning_trace@1`
- one starter lane vocabulary only:
  - `O`
  - `E`
  - `D`
  - `U`
- one starter template-class vocabulary only:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
- one explicit hierarchical posture only:
  - top-level plan spine
  - active parent step
  - explicit child-step set and order law
  - child-step return-to-parent evidence
- one explicit blocked-vs-invalid posture only:
  - lawful blocked / insufficiency
  - invalid early closure
- one deferred-consumer posture only:
  - `V46` may consume these contracts later
  - `V44-A` does not mint benchmark scoring doctrine itself

This slice is contract-first and evidence-first. It does not authorize structural
failure taxonomy release, model-profile aggregation, benchmark metrics, leaderboard
posture, or contest/runtime-selection claims.

## Required Deliverables

The first `V44-A` release should add exactly these live implementation surfaces:

- `packages/adeu_reasoning_assessment/pyproject.toml`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py`
- package schema exports under:
  - `packages/adeu_reasoning_assessment/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_reasoning_assessment/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_reasoning_assessment/tests/fixtures/v44a/`

This slice should not add:

- benchmark metrics or diagnostic-report artifacts;
- benchmark-family or benchmark-projection artifacts;
- structural-failure taxonomy release;
- model structural-reasoning profile release;
- contest-participation or host-adapter surfaces;
- SRM / governor architecture surfaces;
- runtime-routing or role-selection doctrine.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_reasoning_assessment` is the only active implementation package for
  `V44-A`.
- `V41` and `V42` remain released shaping context only.
- `V43` remains a connected but non-reopened planning branch.
- the imported reasoning-benchmark bundle remains support-only shaping evidence.

2. Probe posture

- admit exactly one released probe contract:
  - `adeu_reasoning_template_probe@1`
- each probe must carry:
  - `probe_id`
  - `template_class`
  - `probe_label`
  - `lane_order`
  - explicit template steps
  - acceptance posture
  - optional paired-condition compatibility fields for later `V44-C`
- each probe may be:
  - flat ordered
  - or hierarchical parent/child
- hierarchical probes must carry:
  - explicit top-level plan-spine step ids
  - explicit active parent step ref
  - explicit child-step refs
  - explicit child-order policy
  - explicit return-to-parent required flag
- hierarchical probes in `V44-A` are single-level only:
  - parent + child
  - no nested grandchildren
- out-of-scope in this slice:
  - recursive-depth probes
  - invariance-under-surface-variation probes
  - benchmark instance/context wrappers

3. Trace posture

- admit exactly one released trace contract:
  - `adeu_structural_reasoning_trace@1`
- each trace must carry:
  - `trace_id`
  - `probe_ref`
  - `subject_label`
  - ordered trace events
  - terminal trace status
  - explicit structural-break evidence
  - bounded open-question notes only
- trace events may record only:
  - `step_activate`
  - `step_complete`
  - `branch_select`
  - `blocked`
  - `invalid_early_closure`
  - `repair_enter`
  - `repair_exit`
  - `return_to_parent`
- every trace event must carry:
  - `step_ref`
- every trace event may additionally carry:
  - `lane_ref`
  - bounded `break_tags`
- hierarchical traces must make return-to-parent evidence explicit when local descent
  occurs
- blocked posture must remain distinct from invalid early closure
- terminal `completed_with_structural_break` is only lawful when explicit structural
  break evidence is present
- the trace may carry bounded structural-break evidence, but it may not yet aggregate
  into taxonomy or profile scores

4. Deferred scoring and taxonomy posture

- no benchmark scoring fields in `V44-A`
- no profile dimensions in `V44-A`
- no dominant failure-family aggregation in `V44-A`
- no one-number structural-fidelity summary in `V44-A`
- `V44-B` remains the first lane allowed to mint normalized taxonomy/profile surfaces
- `V44-B` should stay taxonomy-first only
- any model-profile aggregation must remain deferred until `V44-C` or carry explicit
  pre-differential caution posture there
- `V46` remains the first lane allowed to mint benchmark-family / projection scoring
  surfaces

5. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one flat reference probe
  - one hierarchical reference probe
  - one clean reference trace
  - one lawful blocked reference trace
  - one reject trace for invalid early closure posture mismatch
  - one reject trace for invalid hierarchical return evidence
- keep one compact fixture-expectation matrix that states which starter fixtures are
  expected to expose:
  - lane collapse
  - branch collapse
  - plan-spine drift
  - active-step decomposition failure
  - reintegration failure
  - invalid early closure
  - non-local repair drift
- fixture ids and hashes must be canonical and replay-stable

## Bounded Starter Vocabularies

The first `V44-A` release should freeze:

- `template_class`:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
- `lane_id`:
  - `O`
  - `E`
  - `D`
  - `U`
- `trace_event_kind`:
  - `step_activate`
  - `step_complete`
  - `branch_select`
  - `blocked`
  - `invalid_early_closure`
  - `repair_enter`
  - `repair_exit`
  - `return_to_parent`
- `terminal_trace_status`:
  - `completed_clean`
  - `completed_with_structural_break`
  - `blocked`
  - `invalid_early_closure`

Out-of-scope constructs in this slice are:

- benchmark metrics
- benchmark diagnostics
- taxonomy aggregation
- model-profile aggregation
- recursive-depth probe families
- SRM/governor architecture surfaces
- contest/runtime-selection promotion

## Selected Schema Anchors

The first `V44-A` release should freeze at least these probe anchors:

- `schema`
- `probe_id`
- `template_class`
- `probe_label`
- `lane_order`
- `template_steps`
- `acceptance_posture`
- `paired_condition_compatibility`
- `hierarchy_posture`
- `plan_spine_step_ids`
- `active_plan_step_ref`
- `child_step_refs`
- `child_order_policy`
- `return_to_parent_required`

The first `V44-A` release should freeze at least these trace anchors:

- `schema`
- `trace_id`
- `probe_ref`
- `subject_label`
- `trace_events`
- `terminal_trace_status`
- `structural_breaks`
- `open_questions`

## Acceptance

Accept this slice only when:

- the repo-owned package scaffold exists under `packages/adeu_reasoning_assessment`
- both schema families validate and export deterministically
- root `spec/` mirrors exist and match package schema exports
- committed flat and hierarchical reference probes validate cleanly
- committed clean and blocked reference traces validate cleanly
- reject fixtures fail closed for:
  - invalid early closure posture mismatch
  - invalid hierarchical return evidence
- no metrics/taxonomy/profile fields appear in the released `V44-A` contracts
- targeted tests cover canonicalization, ids, schema export, and fixture replay

Do not accept this slice if:

- blocked and invalid early closure are collapsed into one status
- hierarchical probes omit explicit top-level plan spine or return posture
- `V44-A` introduces benchmark metrics or benchmark-family artifacts
- `V44-A` introduces model-profile or taxonomy outputs
- the implementation widens into contest/runtime or SRM doctrine

## Local Gate

- run `make arc-start-check ARC=131` while the bundle remains docs-only
- once source code exists, do not treat this starter bundle as a substitute for the
  full Python lane
