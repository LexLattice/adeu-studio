# Locked Continuation vNext+135

Status: `V44-E` implementation contract.

## V135 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v44e_recursive_depth_assessment_contract@1",
  "target_arc": "vNext+135",
  "target_path": "V44-E",
  "target_scope": "bounded_repo_owned_recursive_depth_and_structural_extension_assessment_over_released_v44a_v44b_and_v44d_prior_to_profile_aggregation_srm_release_or_v46_benchmark_scoring",
  "implementation_packages": [
    "adeu_reasoning_assessment"
  ],
  "governing_released_stack": "V44A_reasoning_assessment_plus_V44B_taxonomy_plus_V44D_probe_suite_on_main",
  "governing_stack_consumption_mode": "released_probe_trace_taxonomy_and_probe_suite_consumer_plus_recursive_extension_assessment_only_no_profile_aggregation_no_srm_release_no_v46_benchmark_scoring",
  "selected_schema_ids": [
    "adeu_recursive_reasoning_assessment@1"
  ],
  "selected_owner_surface": "packages/adeu_reasoning_assessment",
  "consumed_released_schema_ids": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1",
    "adeu_structural_failure_taxonomy@1",
    "adeu_reasoning_probe_suite@1"
  ],
  "starter_recursive_depth_mode": "single_bounded_recursive_reentry_only",
  "max_recursive_extension_depth_selected_here": 1,
  "recursive_self_extension_freeform_not_selected": true,
  "v44c_informative_context_only_not_required_upstream": true,
  "valid_recursive_closure_vs_invalid_early_closure_required": true,
  "recursive_status_judgment_coupling_frozen": true,
  "baseline_invalid_or_under_evidenced_normalizes_only_to_insufficient": true,
  "explicit_recursive_return_to_parent_required": true,
  "non_local_recursive_rewrite_forbidden": true,
  "hierarchical_recursive_reference_required": true,
  "profile_aggregation_selected_here": false,
  "benchmark_projection_consumer_only_deferred_to_v46": true,
  "srm_release_deferred": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v135_closeout.json",
    "artifacts/stop_gate/metrics_v135_closeout.json",
    "artifacts/stop_gate/report_v135_closeout.md"
  ]
}
```

## Objective

Release the bounded `V44-E` recursive-depth seam by defining one repo-owned recursive
assessment contract under `packages/adeu_reasoning_assessment`, consuming released
`V44-A` probes/traces, released `V44-B` taxonomy outputs, and released `V44-D`
probe-suite membership as-is while widening the family into one controlled recursive
re-entry layer only.

`V44-C` remains informative released family context only in this starter slice. It is
not a required upstream contract for `V44-E` starter scope.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_reasoning_assessment`
- one recursive-depth assessment contract only:
  - `adeu_recursive_reasoning_assessment@1`
- one consumed released substrate only:
  - `adeu_reasoning_template_probe@1`
  - `adeu_structural_reasoning_trace@1`
  - `adeu_structural_failure_taxonomy@1`
  - `adeu_reasoning_probe_suite@1`
- one bounded recursive starter posture only:
  - baseline non-recursive execution
  - one recursive re-entry extension beyond the released non-recursive baseline
  - no unbounded or self-amplifying recursion
- one explicit closure posture only:
  - lawful recursive closure
  - recursive closure with bounded structural degradation
  - invalid recursive early closure
- one deferred-consumer posture only:
  - later profile work may consume the released recursive assessment surface
  - `V46` may later consume it for benchmark projections
  - `V44-E` does not mint either lane itself

## Required Deliverables

The first `V44-E` release should add exactly these live implementation surfaces:

- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/recursive_depth.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py`
- package schema exports under:
  - `packages/adeu_reasoning_assessment/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_reasoning_assessment/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_reasoning_assessment/tests/fixtures/v44e/`

This slice should not add:

- model-profile aggregation artifacts;
- cross-model ranking or promotion surfaces;
- one-number structural fidelity summaries;
- benchmark-instance or benchmark-score artifacts;
- SRM governor execution surfaces;
- freeform or unbounded recursive self-extension;
- worker/runtime routing doctrine.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_reasoning_assessment` remains the only active implementation package
  for `V44-E`.
- released `V44-A`, `V44-B`, and `V44-D` contracts remain the only lawful upstream
  sources for recursive-depth assessment.
- released `V44-C` remains informative context only and may not become an ambient
  required input surface in the starter slice.
- the imported benchmarking bundle remains support-only shaping evidence and may not
  define recursive-depth law.

2. Recursive assessment posture

- admit exactly one released recursive assessment contract:
  - `adeu_recursive_reasoning_assessment@1`
- each recursive assessment artifact must carry:
  - `assessment_id`
  - `suite_member_ref`
  - `baseline_probe_ref`
  - `baseline_trace_ref`
  - `baseline_taxonomy_ref`
  - `recursive_probe_ref`
  - `recursive_trace_ref`
  - `recursive_taxonomy_ref`
  - `recursive_depth_mode`
  - `recursive_status`
  - `closure_judgment`
  - ordered `supporting_trace_event_refs`
  - ordered `supporting_failure_families`
  - bounded `open_questions`
- `suite_member_ref` must identify one released `V44-D` suite member and the recursive
  extension must remain semantically anchored to that released baseline member
- `baseline_probe_ref` and `recursive_probe_ref` must share one released procedural
  lineage; recursive assessment may not silently compare unrelated probe skeletons
- `recursive_depth_mode` in the first slice must remain exactly:
  - `single_bounded_recursive_reentry`
- `recursive_status` in the first slice must remain exactly:
  - `recursive_closure_stable`
  - `recursive_closure_degraded`
  - `recursive_early_closure_invalid`
- `closure_judgment` in the first slice must remain exactly:
  - `recursive_extension_lawful`
  - `recursive_extension_structurally_degraded`
  - `recursive_extension_insufficient`
  - `recursive_extension_invalid_early_closure`

3. Recursive-depth law

- the starter slice may widen only to one recursive extension depth beyond the released
  non-recursive baseline
- nested recursive grandchildren beyond that first bounded re-entry remain forbidden
- lawful recursive closure requires:
  - explicit recursive activation evidence
  - explicit return-to-parent evidence
  - no invalid early closure
- strong recursive comparison is admissible only when the baseline posture is itself
  admissible:
  - baseline trace must not close invalidly
  - baseline taxonomy must not be `blocked_lawful_insufficiency`
- `recursive_closure_stable` is lawful only when:
  - the recursive trace closes lawfully
  - the recursive taxonomy does not introduce a new normalized structural failure not
    already present in the baseline posture
- `recursive_closure_degraded` is lawful only when:
  - the recursive trace closes lawfully
  - the recursive taxonomy introduces one or more new normalized structural failures or
    a weaker terminal posture than the baseline
- `recursive_early_closure_invalid` is lawful only when:
  - the recursive trace closes invalidly or lacks required return-to-parent evidence
- status-to-judgment coupling in the first slice must remain exactly:
  - `recursive_closure_stable` may emit only:
    - `recursive_extension_lawful`
    - `recursive_extension_insufficient`
  - `recursive_closure_degraded` may emit only:
    - `recursive_extension_structurally_degraded`
    - `recursive_extension_insufficient`
  - `recursive_early_closure_invalid` may emit only:
    - `recursive_extension_invalid_early_closure`
- `recursive_extension_insufficient` may remain the only lawful judgment when the
  baseline/recursive pair is structurally incomplete or under-evidenced
- if the baseline posture is invalidly closed or under-evidenced, the recursive
  assessment may not emit:
  - `recursive_extension_lawful`
  - `recursive_extension_structurally_degraded`
- non-local recursive rewrite is forbidden:
  - recursive continuation may refine only the active recursive branch and its lawful
    return path
  - it may not globally rewrite unrelated baseline commitments

4. Evidence and ordering law

- `supporting_trace_event_refs` must be trace-qualified and carry:
  - `trace_role`
  - `trace_ref`
  - `event_index`
- `trace_role` in the first slice must remain exactly:
  - `baseline`
  - `recursive_extension`
- `supporting_trace_event_refs` ordering must follow:
  - first supporting occurrence in released trace-event order across baseline first,
    then recursive extension
- `supporting_failure_families` ordering must follow:
  - first supported occurrence in released trace-event order across the same ordered
    trace-role traversal
- hidden heuristic confidence scores are forbidden

5. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one lawful recursive-closure reference pair
  - one degraded-but-lawful recursive-closure reference pair
  - one invalid recursive-early-closure reference pair
  - one positive lawful `recursive_extension_insufficient` reference pair
  - one positive recursive reference pair anchored to a hierarchical released suite
    member
  - one reject fixture for missing recursive return-to-parent evidence
  - one reject fixture for non-local recursive rewrite posture
- keep one compact recursive-mapping matrix showing:
  - released suite member basis
  - baseline versus recursive trace/taxonomy refs
  - recursive status
  - closure judgment

## Bounded Starter Vocabularies

The first `V44-E` release should freeze:

- `recursive_depth_mode`:
  - `single_bounded_recursive_reentry`
- `recursive_status`:
  - `recursive_closure_stable`
  - `recursive_closure_degraded`
  - `recursive_early_closure_invalid`
- `closure_judgment`:
  - `recursive_extension_lawful`
  - `recursive_extension_structurally_degraded`
  - `recursive_extension_insufficient`
  - `recursive_extension_invalid_early_closure`
- `trace_role`:
  - `baseline`
  - `recursive_extension`

## Selected Schema Anchors

The first `V44-E` release should freeze at least these recursive-assessment anchors:

- `schema`
- `assessment_id`
- `suite_member_ref`
- `baseline_probe_ref`
- `baseline_trace_ref`
- `baseline_taxonomy_ref`
- `recursive_probe_ref`
- `recursive_trace_ref`
- `recursive_taxonomy_ref`
- `recursive_depth_mode`
- `recursive_status`
- `closure_judgment`
- `supporting_trace_event_refs`
- `supporting_failure_families`
- `open_questions`

## Acceptance

Accept `V44-E` when:

- one released recursive assessment contract exports and mirrors deterministically
- released `V44-A`, `V44-B`, and `V44-D` surfaces are consumed without semantic
  redefinition
- recursive assessment remains bounded to exactly one recursive re-entry depth
- lawful recursive closure requires explicit recursive return-to-parent evidence
- degraded recursive closure remains distinguishable from invalid recursive early
  closure
- baseline invalidity or under-evidenced posture may normalize only to
  `recursive_extension_insufficient`
- non-local recursive rewrite fails closed
- at least one positive lawful reference exists for stable, degraded, and insufficient
  starter outcomes
- at least one positive recursive reference pair is anchored to a hierarchical
  released suite member
- no profile, benchmark, or SRM-execution surfaces appear in the released contract

Do not accept `V44-E` if:

- recursive assessment silently compares unrelated probe lineages
- recursive continuation allows non-local rewrite of unrelated commitments
- invalid recursive early closure is normalized into a lawful recursive status
- nested recursive grandchildren or unbounded self-extension are introduced
- the slice introduces profiles, rankings, benchmark scoring, or SRM execution
- root `spec/` mirrors are claimed in docs but missing from the released package lane

## Local Gate

- run `make arc-start-check ARC=135`
