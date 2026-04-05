# Locked Continuation vNext+134

Status: `V44-D` implementation contract.

## V134 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v44d_probe_library_widening_contract@1",
  "target_arc": "vNext+134",
  "target_path": "V44-D",
  "target_scope": "bounded_repo_owned_probe_library_widening_across_template_classes_prior_to_profile_aggregation_recursive_depth_or_v46_benchmark_scoring",
  "implementation_packages": [
    "adeu_reasoning_assessment"
  ],
  "governing_released_stack": "V44A_reasoning_assessment_plus_V44B_taxonomy_plus_V44C_differential_on_main",
  "governing_stack_consumption_mode": "released_probe_trace_taxonomy_and_differential_consumer_plus_probe_library_widening_only_no_profile_aggregation_no_v46_benchmark_scoring",
  "selected_schema_ids": [
    "adeu_reasoning_probe_suite@1"
  ],
  "selected_owner_surface": "packages/adeu_reasoning_assessment",
  "consumed_released_schema_ids": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1",
    "adeu_structural_failure_taxonomy@1",
    "adeu_structural_reasoning_differential@1"
  ],
  "selected_template_class_vocabulary": [
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
    "invariance_under_surface_variation"
  ],
  "selected_surface_variation_kind_vocabulary": [
    "paraphrase_preserving",
    "presentation_shift_preserving"
  ],
  "suite_members_first_class_required": true,
  "member_level_consumer_compatibility_required": true,
  "per_class_positive_fixture_coverage_required": true,
  "per_surface_variation_kind_positive_fixture_coverage_required": true,
  "suite_member_ordering_law_frozen": true,
  "suite_hash_subject_frozen": true,
  "repair_locality_posture_frozen": "local_only",
  "recursive_depth_selected_here": false,
  "profile_aggregation_selected_here": false,
  "benchmark_projection_consumer_only_deferred_to_v46": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v134_closeout.json",
    "artifacts/stop_gate/metrics_v134_closeout.json",
    "artifacts/stop_gate/report_v134_closeout.md"
  ]
}
```

## Objective

Release the bounded `V44-D` probe-library widening seam by defining one repo-owned
probe-suite contract under `packages/adeu_reasoning_assessment`, widening the released
probe library across decomposition, branching, repair, and invariance classes while
continuing to consume released `V44-A`, `V44-B`, and `V44-C` surfaces as-is.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_reasoning_assessment`
- one probe-suite contract only:
  - `adeu_reasoning_probe_suite@1`
- one consumed released substrate only:
  - `adeu_reasoning_template_probe@1`
  - `adeu_structural_reasoning_trace@1`
  - `adeu_structural_failure_taxonomy@1`
  - `adeu_structural_reasoning_differential@1`
- one widened template-class vocabulary only:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
  - `invariance_under_surface_variation`
- one first-class suite-membership posture only:
  - each released member must bind one released probe to one released template class
  - optional surface variation and repair-locality posture must live on the member,
    not only in suite-level summaries
  - consumer compatibility must be declared per member, not as a blanket suite claim
- one bounded surface-variation posture only:
  - `paraphrase_preserving`
  - `presentation_shift_preserving`
- one bounded repair posture only:
  - local repair only
- one deferred-consumer posture only:
  - later profile work may consume the widened library
  - `V46` may later consume it for benchmark projections
  - `V44-D` does not mint either lane itself

## Required Deliverables

The first `V44-D` release should add exactly these live implementation surfaces:

- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/probe_library.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py`
- package schema exports under:
  - `packages/adeu_reasoning_assessment/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_reasoning_assessment/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_reasoning_assessment/tests/fixtures/v44d/`

This slice should not add:

- model-profile aggregation artifacts;
- cross-model ranking or promotion surfaces;
- one-number structural-fidelity summaries;
- benchmark-instance or benchmark-score artifacts;
- recursive-depth / nested-grandchild probes;
- worker/runtime-routing doctrine;
- contest/runtime selection claims.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_reasoning_assessment` remains the only active implementation package
  for `V44-D`.
- released `V44-A`, `V44-B`, and `V44-C` contracts remain the only lawful upstream
  sources for probe-library widening.
- the imported benchmarking bundle remains support-only shaping evidence and may not
  define probe-library law.

2. Probe-suite posture

- admit exactly one released suite contract:
  - `adeu_reasoning_probe_suite@1`
- each suite artifact must carry:
  - `suite_id`
  - `suite_label`
  - ordered `suite_members`
  - `template_classes_included`
  - `accepted_surface_variation_kinds`
  - `repair_locality_posture`
  - `suite_hash`
- each `suite_member` must carry:
  - `probe_ref`
  - `template_class`
  - optional `surface_variation_kind`
  - optional `repair_locality_posture`
  - ordered `consumer_compatibility_refs`
  - `paired_condition_compatible`
- `probe_ref` values may reference only released probes that validate under
  `adeu_reasoning_template_probe@1`
- member `consumer_compatibility_refs` may point only to released taxonomy or
  differential surfaces, or to committed suite-matrix evidence that names the same
  released surfaces; they may not embed benchmark, ranking, or profile outputs
- suite-level summaries are derived from `suite_members` only:
  - `template_classes_included` may list only classes present in `suite_members`
  - `accepted_surface_variation_kinds` may list only kinds present in `suite_members`
- `template_classes_included` in the first slice must include exactly:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
  - `invariance_under_surface_variation`
- at least one released suite member must exist for each frozen starter template class
- at least one released invariance suite member must exist for each frozen
  `surface_variation_kind`
- `repair_locality_posture` at suite level is a bounded suite summary only:
  - it may restate only the member-level posture selected in the first slice
  - in the starter slice that summary must remain `local_only`

3. Widening law

- the first slice may widen probe-library coverage only by:
  - adding new released probes/traces that preserve the released `V44-A` contract law
  - adding invariance probes that preserve one abstract procedure while varying only a
    frozen surface-variation kind
  - adding local-repair suites that preserve unaffected lanes and commitments while
    repairing one bounded defect
- invariance probes must carry explicit procedure-preservation anchors and may not rely
  on answer equivalence alone
- local-repair suites must remain local-only and may not silently normalize chaotic
  global rewrite as lawful repair
- recursive-depth or nested-grandchild hierarchy remains forbidden in `V44-D`
- hidden heuristic confidence scores are forbidden

4. Consumer-compatibility posture

- `V44-D` may validate that widened-library fixtures remain consumable by released
  `V44-B` and released `V44-C` helpers
- `V44-D` may not redefine released taxonomy or differential semantics while doing so
- paired-condition doctrine remains bounded to released `V44-C`
- consumer compatibility must remain granular at member level:
  - some members may be lawful for released `V44-B` taxonomy consumption only
  - some members may also be lawful for released `V44-C` differential consumption
  - invariance or repair members may remain non-pair-compatible
- `paired_condition_compatible` may be `true` only when the referenced released probe
  already advertises lawful paired-condition compatibility under `V44-A`
- no profile, ranking, or benchmark fields may appear in the released suite contract

5. Ordering and hash law

- `template_classes_included` ordering must follow:
  - frozen `template_class` vocabulary order
- `accepted_surface_variation_kinds` ordering must follow:
  - frozen `surface_variation_kind` vocabulary order
- `suite_members` ordering must follow this canonical tuple:
  - `template_class` vocabulary order
  - `surface_variation_kind` vocabulary order, with no variation before any variation
  - `probe_ref` lexicographic order
- member `consumer_compatibility_refs` ordering must follow:
  - released-surface grouping first:
    - taxonomy-compatible refs
    - differential-compatible refs
  - then lexicographic order within each group
- `suite_hash` must be computed from canonical JSON over the ordered suite artifact
  subject with `suite_hash` excluded from the hash subject itself

6. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one reference suite manifest
  - one new branching reference probe/trace pair
  - one new local-repair reference probe/trace pair
  - one new invariance reference probe/trace pair for
    `paraphrase_preserving`
  - one new invariance reference probe/trace pair for
    `presentation_shift_preserving`
  - one compatibility replay reference showing widened-library consumption through
    released `V44-B` taxonomy only
  - one compatibility replay reference showing widened-library consumption through
    released `V44-C` differential where pair compatibility is lawful
  - one reject fixture for invalid procedure-preservation anchors in an invariance
    suite
  - one reject fixture for non-local repair rewrite posture
- keep one compact suite matrix showing:
  - probe-to-template-class assignment
  - admitted surface-variation kind when present
  - admitted consumer compatibility posture per member

## Bounded Starter Vocabularies

The first `V44-D` release should freeze:

- `template_class`:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
  - `invariance_under_surface_variation`
- `surface_variation_kind`:
  - `paraphrase_preserving`
  - `presentation_shift_preserving`
- `repair_locality_posture`:
  - `local_only`

## Selected Schema Anchors

The first `V44-D` release should freeze at least these suite anchors:

- `schema`
- `suite_id`
- `suite_label`
- `suite_members`
- `template_classes_included`
- `accepted_surface_variation_kinds`
- `repair_locality_posture`
- `suite_hash`

The first `V44-D` release should freeze at least these suite-member anchors:

- `probe_ref`
- `template_class`
- `surface_variation_kind`
- `repair_locality_posture`
- `consumer_compatibility_refs`
- `paired_condition_compatible`

## Acceptance

Accept `V44-D` when:

- one released probe-suite contract exports and mirrors deterministically
- suite membership semantics are first-class in the released contract rather than
  externalized only in fixture prose or matrices
- widened-library probes continue to validate under released `V44-A` probe/trace law
- invariance probes preserve an explicit abstract procedure under only the admitted
  surface-variation kinds
- at least one released suite member exists for each frozen starter template class
- at least one positive released invariance member exists for each frozen
  `surface_variation_kind`
- local-repair probes keep repair locality bounded and explicit
- widened-library compatibility remains granular and explicit at member level
- at least one widened-library compatibility replay remains lawful through released
  `V44-B`
- at least one widened-library compatibility replay remains lawful through released
  `V44-C` where pair compatibility is lawful
- no profile, ranking, benchmark, or recursive-depth surfaces appear in the released
  contract

Do not accept `V44-D` if:

- answer equivalence is treated as a substitute for explicit procedure-preservation
  anchors
- local-repair suites silently allow non-local rewrite
- suite-wide blanket compatibility claims replace member-level compatibility law
- recursive-depth or nested-grandchild probes are introduced
- the slice silently redefines released `V44-B` taxonomy or released `V44-C`
  differential law
- root `spec/` mirrors are claimed in docs but missing from the released package lane
