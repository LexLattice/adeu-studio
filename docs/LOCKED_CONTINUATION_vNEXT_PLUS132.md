# Locked Continuation vNext+132

Status: `V44-B` implementation contract.

## V132 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v44b_structural_failure_taxonomy_contract@1",
  "target_arc": "vNext+132",
  "target_path": "V44-B",
  "target_scope": "bounded_repo_owned_structural_failure_taxonomy_prior_to_paired_condition_differential_profile_aggregation_or_benchmark_scoring",
  "implementation_packages": [
    "adeu_reasoning_assessment"
  ],
  "governing_released_stack": "V44A_reasoning_assessment_on_main",
  "governing_stack_consumption_mode": "released_probe_trace_consumer_only_no_v46_benchmark_scoring_no_v44c_differential_profile_doctrine",
  "selected_schema_ids": [
    "adeu_structural_failure_taxonomy@1"
  ],
  "selected_owner_surface": "packages/adeu_reasoning_assessment",
  "consumed_released_schema_ids": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1"
  ],
  "normalized_failure_family_vocabulary": [
    "lane_collapse",
    "branch_collapse",
    "plan_spine_drift",
    "active_step_decomposition_failure",
    "reintegration_failure",
    "invalid_early_closure",
    "non_local_repair_drift"
  ],
  "blocked_posture_preservation_required": true,
  "trace_break_mapping_mode": "released_v44a_trace_and_fixture_expectation_consumer_only_fail_closed_on_unmapped_structural_breaks",
  "failure_family_ordering_law": "first_supported_occurrence_in_released_trace_event_order",
  "one_number_structural_fidelity_forbidden": true,
  "profile_fields_forbidden_in_v44b": true,
  "paired_condition_differential_deferred_to_v44c": true,
  "benchmark_projection_consumer_only_deferred_to_v46": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v132_closeout.json",
    "artifacts/stop_gate/metrics_v132_closeout.json",
    "artifacts/stop_gate/report_v132_closeout.md"
  ]
}
```

## Objective

Release the bounded `V44-B` taxonomy-first seam by defining one repo-owned structural
failure taxonomy contract under `packages/adeu_reasoning_assessment`, consuming only
released `V44-A` probes, traces, and deterministic fixture expectations, while still
forbidding paired-condition diagnosis, model-profile aggregation, benchmark scoring,
or any one-number structural-fidelity promotion posture.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_reasoning_assessment`
- one taxonomy artifact contract only:
  - `adeu_structural_failure_taxonomy@1`
- one consumed released substrate only:
  - `adeu_reasoning_template_probe@1`
  - `adeu_structural_reasoning_trace@1`
- one normalized starter failure-family vocabulary only:
  - `lane_collapse`
  - `branch_collapse`
  - `plan_spine_drift`
  - `active_step_decomposition_failure`
  - `reintegration_failure`
  - `invalid_early_closure`
  - `non_local_repair_drift`
- one explicit blocked-posture preservation law only:
  - lawful blocked traces remain non-failure outcomes
  - they must not be silently coerced into failure-family claims
- one deferred-consumer posture only:
  - `V44-C` may later consume this taxonomy for paired-condition differential diagnosis
  - `V46` may later consume it for benchmark projections
  - `V44-B` does not mint either lane itself

## Required Deliverables

The first `V44-B` release should add exactly these live implementation surfaces:

- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/taxonomy.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py`
- package schema exports under:
  - `packages/adeu_reasoning_assessment/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_reasoning_assessment/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_reasoning_assessment/tests/fixtures/v44b/`

This slice should not add:

- paired supplied-knowledge versus withheld-knowledge differential outputs;
- injected-knowledge continuation doctrine;
- model profile or model ranking surfaces;
- benchmark-instance or benchmark-score artifacts;
- contest/runtime selection claims;
- recursive-depth assessment;
- broader probe-library widening beyond released `V44-A` starter probes.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_reasoning_assessment` remains the only active implementation package
  for `V44-B`.
- released `V44-A` contracts remain the only lawful upstream source for taxonomy
  normalization.
- the imported benchmarking bundle remains support-only shaping evidence and may not
  define taxonomy law.

2. Taxonomy posture

- admit exactly one released taxonomy contract:
  - `adeu_structural_failure_taxonomy@1`
- each taxonomy artifact must carry:
  - `taxonomy_id`
  - `probe_ref`
  - `trace_ref`
  - `taxonomy_status`
  - `terminal_trace_status`
  - ordered `failure_families`
  - optional `primary_failure_family`
  - bounded `supporting_break_refs`
  - bounded `supporting_event_indexes`
  - bounded `open_questions`
- each taxonomy artifact may describe exactly one of these outcome postures:
  - clean completion with no normalized structural failure
  - lawful blocked insufficiency with no normalized structural failure
  - normalized structural failure
- for `completed_clean_no_failure`:
  - `failure_families = []`
  - `primary_failure_family` absent
  - `supporting_break_refs = []`
  - `supporting_event_indexes = []`
- for `blocked_lawful_insufficiency`:
  - `failure_families = []`
  - `primary_failure_family` absent
  - `supporting_break_refs = []`
  - `supporting_event_indexes = []`
- for `normalized_structural_failure`:
  - `failure_families` must be non-empty
  - `primary_failure_family`, if present, must be a member of `failure_families`
- blocked posture must remain distinct from failure-family assignment
- invalid early closure may normalize only to:
  - `invalid_early_closure`

3. Mapping law

- taxonomy may consume only:
  - released probe structure
  - released trace structure
  - released fixture expectation surfaces from `V44-A`
- unsupported structural break tags, unsupported event combinations, or missing released
  anchors must fail closed
- released `V44-A` starter fixtures are the only admitted mapping baseline in this
  slice
- no hidden heuristic confidence scoring is allowed
- `failure_families` ordering must follow:
  - first supported occurrence in released trace-event order
- `supporting_event_indexes` ordering must follow:
  - ascending released `event_index` order with duplicates removed

4. Deferred diagnosis/profile posture

- no knowledge-versus-procedure differential claims in `V44-B`
- no supplied-versus-withheld paired-condition outputs in `V44-B`
- no model-profile aggregation in `V44-B`
- no one-number structural fidelity score in `V44-B`
- no benchmark projection or leaderboard output in `V44-B`
- `V44-C` remains the first lane allowed to mint paired-condition differential and any
  explicitly pre-differential profile lane
- `V46` remains the first lane allowed to mint benchmark-family projection surfaces

5. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one clean no-failure taxonomy reference
  - one lawful blocked taxonomy reference
  - one normalized `plan_spine_drift` taxonomy reference
  - one normalized `active_step_decomposition_failure` taxonomy reference
  - one normalized `reintegration_failure` taxonomy reference
  - one reject fixture for unsupported break-tag mapping
  - one reject fixture for blocked trace coerced into failure-family output
- keep one compact taxonomy-mapping matrix showing which released `V44-A` surfaces map
  to which normalized failure families in the starter slice

## Bounded Starter Vocabularies

The first `V44-B` release should freeze:

- `taxonomy_status`:
  - `completed_clean_no_failure`
  - `blocked_lawful_insufficiency`
  - `normalized_structural_failure`
- `failure_family`:
  - `lane_collapse`
  - `branch_collapse`
  - `plan_spine_drift`
  - `active_step_decomposition_failure`
  - `reintegration_failure`
  - `invalid_early_closure`
  - `non_local_repair_drift`

## Selected Schema Anchors

The first `V44-B` release should freeze at least these taxonomy anchors:

- `schema`
- `taxonomy_id`
- `probe_ref`
- `trace_ref`
- `taxonomy_status`
- `terminal_trace_status`
- `failure_families`
- `primary_failure_family`
- `supporting_break_refs`
- `supporting_event_indexes`
- `open_questions`

## Acceptance

Accept `V44-B` when:

- released `V44-A` probes/traces are consumed without redefining their semantics
- clean traces normalize to no-failure taxonomy outputs deterministically
- lawful blocked traces normalize to blocked outcomes without failure-family drift
- released starter structural breaks normalize to the frozen failure-family vocabulary
- unsupported break tags or unsupported mappings fail closed
- no profile, benchmark, or one-number score fields appear in the released contract
- authoritative and mirror schemas export deterministically

Do not accept `V44-B` if:

- blocked traces are silently normalized into failure-family outputs
- taxonomy output depends on non-released heuristic signals
- the slice introduces knowledge-versus-procedure diagnosis
- the slice introduces model profiles, rankings, or benchmark scoring
- root `spec/` mirrors are claimed in docs but missing from the released package lane
