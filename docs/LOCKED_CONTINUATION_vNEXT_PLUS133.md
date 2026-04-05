# Locked Continuation vNext+133

Status: `V44-C` implementation contract.

## V133 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v44c_paired_condition_differential_contract@1",
  "target_arc": "vNext+133",
  "target_path": "V44-C",
  "target_scope": "bounded_repo_owned_paired_condition_differential_diagnosis_over_released_v44a_and_v44b_prior_to_profile_aggregation_or_v46_benchmark_scoring",
  "implementation_packages": [
    "adeu_reasoning_assessment"
  ],
  "governing_released_stack": "V44A_reasoning_assessment_and_V44B_taxonomy_on_main",
  "governing_stack_consumption_mode": "released_probe_trace_and_taxonomy_consumer_only_no_profile_aggregation_no_v46_benchmark_scoring",
  "selected_schema_ids": [
    "adeu_structural_reasoning_differential@1"
  ],
  "selected_owner_surface": "packages/adeu_reasoning_assessment",
  "consumed_released_schema_ids": [
    "adeu_reasoning_template_probe@1",
    "adeu_structural_reasoning_trace@1",
    "adeu_structural_failure_taxonomy@1"
  ],
  "starter_condition_role_vocabulary": [
    "supplied_knowledge",
    "withheld_knowledge"
  ],
  "optional_support_condition_role_vocabulary": [
    "injected_knowledge_continuation"
  ],
  "differential_judgment_vocabulary": [
    "knowledge_deficit_supported",
    "procedural_discipline_deficit_supported",
    "mixed_or_ambiguous",
    "paired_condition_insufficient"
  ],
  "paired_condition_compatibility_required": true,
  "trace_qualified_supporting_event_refs_required": true,
  "differential_status_judgment_coupling_frozen": true,
  "injected_knowledge_support_non_overriding_required": true,
  "profile_aggregation_selected_here": false,
  "benchmark_projection_consumer_only_deferred_to_v46": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v133_closeout.json",
    "artifacts/stop_gate/metrics_v133_closeout.json",
    "artifacts/stop_gate/report_v133_closeout.md"
  ]
}
```

## Objective

Release the bounded `V44-C` paired-condition differential seam by defining one
repo-owned differential diagnosis contract under `packages/adeu_reasoning_assessment`,
consuming only released `V44-A` probe/trace contracts and released `V44-B` taxonomy
artifacts, while still forbidding model-profile aggregation, benchmark scoring, or any
promotion posture beyond bounded pair-level diagnosis.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_reasoning_assessment`
- one differential diagnosis contract only:
  - `adeu_structural_reasoning_differential@1`
- one consumed released substrate only:
  - `adeu_reasoning_template_probe@1`
  - `adeu_structural_reasoning_trace@1`
  - `adeu_structural_failure_taxonomy@1`
- one starter paired-condition requirement only:
  - `supplied_knowledge`
  - `withheld_knowledge`
- one optional support condition posture only:
  - `injected_knowledge_continuation`
- one bounded starter differential judgment vocabulary only:
  - `knowledge_deficit_supported`
  - `procedural_discipline_deficit_supported`
  - `mixed_or_ambiguous`
  - `paired_condition_insufficient`
- one deferred-consumer posture only:
  - later profile aggregation may consume the released differential surface
  - `V46` may later consume it for benchmark projections
  - `V44-C` does not mint either lane itself in the starter slice

## Required Deliverables

The first `V44-C` release should add exactly these live implementation surfaces:

- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/differential.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py`
- `packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py`
- package schema exports under:
  - `packages/adeu_reasoning_assessment/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_reasoning_assessment/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_reasoning_assessment/tests/fixtures/v44c/`

This slice should not add:

- model-profile aggregation artifacts;
- cross-model ranking or promotion surfaces;
- one-number structural fidelity summaries;
- benchmark-instance or benchmark-score artifacts;
- recursive-depth assessment;
- probe-library widening beyond the released `V44-A` starter probes;
- contest/runtime selection claims.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_reasoning_assessment` remains the only active implementation package
  for `V44-C`.
- released `V44-A` and released `V44-B` contracts remain the only lawful upstream
  sources for paired-condition differential diagnosis.
- the imported benchmarking bundle remains support-only shaping evidence and may not
  define paired-condition law.

2. Pairing posture

- admit exactly one released differential contract:
  - `adeu_structural_reasoning_differential@1`
- each differential artifact must carry:
  - `differential_id`
  - `probe_template_ref`
  - `condition_trace_refs`
  - `condition_taxonomy_refs`
  - `condition_roles_present`
  - `differential_status`
  - `differential_judgment`
  - `supporting_failure_families`
  - `supporting_trace_event_refs`
  - `open_questions`
- `probe_template_ref` must identify the shared released probe-template lineage that
  grounds the admitted pair; it may not silently point to only one condition-specific
  probe instance
- starter `condition_roles_present` must include exactly:
  - `supplied_knowledge`
  - `withheld_knowledge`
- `injected_knowledge_continuation` may appear only as bounded supporting evidence in
  the first slice; it may not become required for all starter diagnostics and may not
  override the starter supplied/withheld pair law by itself
- all paired traces/taxonomies must reference probes that advertise released
  `paired_condition_compatibility`
- incompatible template refs, incompatible compatibility posture, or missing required
  roles must fail closed

3. Differential law

- `knowledge_deficit_supported` is lawful only when:
  - `differential_status = paired_conditions_complete`
  - supplied `taxonomy_status = completed_clean_no_failure`
  - withheld `taxonomy_status = blocked_lawful_insufficiency`
- `procedural_discipline_deficit_supported` is lawful only when:
  - `differential_status = paired_conditions_complete`
  - supplied `taxonomy_status = normalized_structural_failure`
- `mixed_or_ambiguous` is lawful only when:
  - `differential_status = paired_conditions_complete`
  - the admitted pair does not satisfy the frozen laws for
    `knowledge_deficit_supported` or `procedural_discipline_deficit_supported`
- `paired_condition_insufficient` is lawful only when:
  - the starter pair is incomplete, incompatible, or complete but still too
    underdetermined to support a stronger judgment
- `paired_conditions_incomplete` may emit only:
  - `paired_condition_insufficient`
- `paired_conditions_incompatible` may emit only:
  - `paired_condition_insufficient`
- only `paired_conditions_complete` may emit:
  - `knowledge_deficit_supported`
  - `procedural_discipline_deficit_supported`
  - `mixed_or_ambiguous`
- the first slice may consume only:
  - released paired-condition compatibility posture from `V44-A`
  - released trace structure from `V44-A`
  - released taxonomy structure from `V44-B`
- hidden heuristic confidence scores are forbidden
- `supporting_failure_families` ordering must follow:
  - first supported occurrence in released trace-event order across the admitted pair
- `supporting_trace_event_refs` must be trace-qualified:
  - each item must carry `condition_role`
  - each item must carry `trace_ref`
  - each item must carry `event_index`
- `supporting_trace_event_refs` ordering must follow:
  - first supporting occurrence in released trace-event order across the admitted pair

4. Optional injected-knowledge support posture

- if `injected_knowledge_continuation` is present, it may only support a judgment that
  is already lawful under the starter supplied/withheld pair law
- it may not independently upgrade `paired_condition_insufficient` or
  `mixed_or_ambiguous` into a stronger starter judgment

5. Deferred profile/benchmark posture

- no model-profile aggregation artifact is released in `V44-C` starter scope
- no cross-model or per-model ranking surface is released in `V44-C`
- no one-number structural fidelity score is released in `V44-C`
- no benchmark projection or leaderboard output is released in `V44-C`
- any later profile lane must consume the released `V44-C` differential artifact rather
  than being silently embedded here
- `V46` remains the first lane allowed to mint benchmark-family projection surfaces

6. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one reference pair supporting `knowledge_deficit_supported`
  - one reference pair supporting `procedural_discipline_deficit_supported`
  - one reference pair supporting `mixed_or_ambiguous`
  - one reference pair supporting `paired_condition_insufficient`
  - one reject fixture for incompatible pair compatibility posture
  - one reject fixture for missing required starter condition role
- keep one compact differential-mapping matrix showing which released `V44-A` and
  `V44-B` surfaces support each starter differential judgment

## Bounded Starter Vocabularies

The first `V44-C` release should freeze:

- `condition_role`:
  - `supplied_knowledge`
  - `withheld_knowledge`
  - `injected_knowledge_continuation`
- `differential_status`:
  - `paired_conditions_complete`
  - `paired_conditions_incomplete`
  - `paired_conditions_incompatible`
- `differential_judgment`:
  - `knowledge_deficit_supported`
  - `procedural_discipline_deficit_supported`
  - `mixed_or_ambiguous`
  - `paired_condition_insufficient`

## Selected Schema Anchors

The first `V44-C` release should freeze at least these differential anchors:

- `schema`
- `differential_id`
- `probe_template_ref`
- `condition_trace_refs`
- `condition_taxonomy_refs`
- `condition_roles_present`
- `differential_status`
- `differential_judgment`
- `supporting_failure_families`
- `supporting_trace_event_refs`
- `open_questions`

## Acceptance

Accept `V44-C` when:

- released `V44-A` probes/traces and released `V44-B` taxonomies are consumed without
  redefining their semantics
- starter paired conditions normalize deterministically to the frozen differential
  judgment vocabulary
- compatible supplied-versus-withheld pairs can distinguish starter
  knowledge-deficit versus procedural-discipline postures
- incomplete or incompatible pairs fail closed or normalize only to
  `paired_condition_insufficient`
- no profile, benchmark, or one-number score fields appear in the released contract
- authoritative and mirror schemas export deterministically

Do not accept `V44-C` if:

- the slice silently embeds model-profile aggregation or promotion posture
- the slice consumes non-released pair semantics or heuristic scores
- incompatible pairings are silently accepted
- the slice introduces benchmark scoring or benchmark-family projection
- root `spec/` mirrors are claimed in docs but missing from the released package lane

## Local Gate

- run `make arc-start-check ARC=133`
