# Draft Arc Series Multi-Layer Mapping v1

Status: support-layer empirical hardening draft over
`docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md`.

Authority layer: support.

This document does not supersede any selector, lock, architecture, implementation
mapping, closeout artifact, released schema, or runtime contract. It supersedes only
the support synthesis in `v0` for the purpose of naming the current best missing arc
set. The core eight-family set from `v0` remains intact, but `V68` is hardened after
an empirical stress run over repo-native reasoning support tools.

## What Changed From v0

- The map now distinguishes three arc namespaces as a required future contract:
  selector version, family arc, and implementation/evidence arc.
- `V68` is widened from a plain arc graph and closure registry into arc cartography,
  namespace disambiguation, tool-applicability, and closure registry.
- The proof sketch now has an empirical seam test: every missing family must explain
  at least one observed inability of the current repo to complete the recursive
  self-improvement loop with already instantiated tools.
- The machine-readable seed is upgraded to
  `adeu_arc_series_multi_layer_mapping@1` and records actual tool outcomes rather
  than only the proposed family names.

## Epistemic Stress Loop

The loop used for this hardening pass is adapted from:

- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_PRACTICAL_INTENT_STRESS_SIX_LANE_LOOP_v0.md`
- `docs/templates/PRACTICAL_INTENT_STRESS_SIX_LANE_RESULT_TEMPLATE_v0.json`

Frozen world:

- target object: `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md`;
- authoritative source family: selector docs through
  `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md`, family mapping docs, closeout docs, and
  committed evidence artifacts already referenced by `v0`;
- accepted support docs: intent authority layering, horizon glossary, future seam
  promotion rules, practical harness flow, practical reasoning loop, practical
  intent-stress loop, recursive-coordinate placement docs, ANM practice docs, and
  resident-agent family docs;
- explicit exclusions: web lookup, external services, destructive mutation scripts,
  runtime action widening scripts, and treating a clean exit code as proof of
  conceptual completeness.

Method:

1. Freeze the `v0` claims: phase map, cross-layer map, eight missing families, and
   proof sketch.
2. Inventory instantiated repo tools that claim to support reasoning, intent,
   closure, semantic compilation, constitutional coherence, test selection, or arc
   dependency mapping.
3. Run the promising tools in read-only or check mode where possible, writing scratch
   outputs under `/tmp`.
4. Classify each result as `validates`, `constrains`, `not_applicable`,
   `stale_or_mismatched`, or `local_sanity_only`.
5. Patch the missing-family map only where empirical results expose a real missing
   seam.

## Empirical Findings

| Tool or surface | Intended usefulness | Observed result | Utility judgment | Consequence |
|---|---|---|---|---|
| `make arc-closeout-check ARC=67` | Validate docs/artifacts-only closeout posture for an arc bundle. | Passed: `arc_bundle_lint@1` had no failures, closeout consistency had no failures, `semantic_compiler_closeout_lint@1` had no failures, and generated instruction policy views verified. | Useful, but namespace-limited. `ARC=67` targets historical `vNEXT_PLUS67`, not family `V67`. | `V68` must make selector, family, and implementation/evidence arc namespaces explicit before downstream closure claims. |
| `apps/api/scripts/lint_recursive_coordinate_warnings.py` on default docs | Validate embedded `recursive_schema_coordinate@1` pilot records. | Passed over 14 records with zero warnings. | Useful for coordinate-bearing markdown. | Existing coordinate lint is real and should be reused where future arc cartography emits coordinate records. |
| `apps/api/scripts/lint_recursive_coordinate_warnings.py --doc docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md` | Check whether the new map already has recursive-coordinate shape. | Passed with `checked_record_count: 0`. | Negative evidence. It did not evaluate the map; it found no coordinate records. | `V68` needs either explicit coordinate records or an explicit `coordinate_absence` posture. |
| `adeu_semantic_source.compile_semantic_source(... write_outputs=False)` on `v0` | Detect semantic-source diagnostics over the support doc. | Succeeded with zero diagnostics, one semantic file, zero semantic blocks, and zero frontmatter semantic records. | Constrains the claim. The doc is acceptable as markdown input, but not an ANM semantic source. | Future arc-series mapping should not pretend prose support docs are semantic-source artifacts unless they emit owned blocks. |
| `adeu_semantic_compiler.compile_semantic_compiler(write_outputs=False)` | Confirm current semantic compiler baseline health. | Succeeded with diagnostics payload empty and no changed surfaces. Initial caller assumption that the result had a top-level `.diagnostics` field failed; diagnostics live inside `diagnostics_payload`. | Useful baseline check, not map-specific. The API shape itself is evidence that tool integration must be explicit. | `V70` should classify tool outputs by real schema/API shape, not by assumed names. |
| `apps/api/scripts/lint_constitutional_coherence_v55a.py` | Run starter constitutional coherence checker over admitted seed set. | Exited 0 and produced `constitutional_coherence_report@1` plus `constitutional_unresolved_seam_register@1` with 7 entries, all `not_evaluable_yet`. | Useful but advisory and seed-bound. It does not evaluate `v0` unless `v0` becomes admitted support. | `V70` and `V71` must keep advisory, warning-only, and gating authority distinct. |
| `apps/api/scripts/lint_constitutional_coherence_v55c.py` | Run advisory governance and migration decision checker. | Exited 0; governance register had 3 entries and migration register had 6 entries. Both advertise `advisory_only`; migration keeps checker exit codes warning-only. | Useful evidence for constitutional migration posture. | Recursive integration cannot treat coherence warnings as hard gates until a later authority surface selects that migration. |
| `adeu_repo_description.test_selection_v0 --changed-path docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md` | Select relevant tests for the new support doc. | Produced `repo_test_selection_plan@2`, `risk_posture: narrow`, selected `packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py`, and did not recommend the full suite. | Useful but approximate. It classified the new doc through an artifact/fixture witness rather than a dedicated arc-map witness. | `V68` or `V70` needs dedicated arc-map dependency witnesses. |
| Selected pytest from the test selector | Check the one selected semantic compiler guard test. | Passed: 35 tests completed. One unbounded rerun printed full test completion and warnings, then the process did not exit; a timeout-bound rerun exited cleanly with code 0. | Good local validation, with an operational runner anomaly recorded. | Confirms no immediate semantic compiler guard regression from the new support doc and reinforces the need to record tool fitness separately from test assertions. |
| `packages/adeu_reasoning_assessment` targeted tests | Check released structural reasoning assessment model and recursive-depth support. | Passed: 18 tests completed, with deprecation warnings from repo-root discovery. | Useful baseline. It validates V44-style reasoning assessment contracts, but not the arc-series map itself. | `V70` can consume this package for candidate quality evaluation, but still needs a recursive candidate classifier. |
| `packages/adeu_repo_description/tests/test_repo_description_v45c.py` | Validate repo arc dependency register schemas and historical fixtures. | Passed: 24 tests completed. | Useful schema and fixture baseline. | `V68` should reuse the schema lessons from `repo_arc_dependency_register@2`. |
| `derive_v45c_repo_arc_dependency_register()` | Attempt direct live derivation of a current arc dependency register. | Failed with `ValueError`: the extractor requires V45-B to remain the broader selected branch in planning. | Stale or horizon-mismatched for current full-series cartography. | `V68` cannot simply call the V45-C extractor and claim current arc closure. It needs a current extractor or compatibility layer. |
| Local JSON block parser over `v0` | Sanity-check embedded machine-readable seed. | Parsed one JSON block with schema `adeu_arc_series_multi_layer_mapping@0`; the missing set is present as 8 strings under `minimal_missing_family_set`. | Local sanity only, not a repo-native schema validation. | `v1` should emit a richer schema seed with typed family records and empirical tool results. |

The agentic resident-runtime scripts from `V56` through `V65` were not run in this
stress pass. They are relevant to future execution widening, but they are runtime
effect tools rather than support-layer reasoning checks for this doc. Their proper
place is `V72` contained trial/integration and `V75` governed dispatch widening, not
this support-doc hardening run.

## Hardened Missing Family Set

The optimal family set remains eight families. The empirical pass changes the first
family and sharpens several downstream boundaries; it does not justify a ninth
family.

| Proposed family | Hardened seam | New empirical driver | Primary outputs | Boundary |
|---|---|---|---|---|
| `V68` | arc cartography, namespace disambiguation, tool-applicability, and closure registry | `ARC=67` closeout namespace mismatch; V45-C live extractor failure; zero coordinate records in `v0` | `adeu_arc_namespace_map@1`, `adeu_arc_series_graph@1`, `adeu_family_closure_register@1`, `adeu_selector_lineage_report@1`, `arc_mapping_tool_applicability_report@1`, `recursive_coordinate_emission_plan@1` | support/planning graph only, no runtime authority |
| `V69` | recursive candidate advancement intake and O/E/D/U mapping | semantic-source compiler sees support prose but no semantic blocks | `recursive_candidate_advancement_record@1`, `recursive_odeu_mapping@1`, `candidate_source_provenance_packet@1` | describe/map only, no adoption decision |
| `V70` | integration-class classifier, quality threshold evaluator, and evidence/tool-result classifier | constitutional checks are advisory; test selection is approximate; compiler API shape must be read, not guessed | `recursive_integration_classification@1`, `recursive_quality_threshold_report@1`, `integration_risk_register@1`, `tool_result_applicability_judgment@1` | evaluates evidence and class, but cannot ratify |
| `V71` | amendment, ratification, and human-internal authority kernel | V55-C keeps migration decisions advisory-only; warning checks do not mint gates | `recursive_ratification_request@1`, `recursive_ratification_record@1`, `amendment_scope_boundary@1`, `human_role_authority_profile@1` | decision/ratification only, no implementation by itself |
| `V72` | contained trial, integration, and rollback harness | runtime agentic scripts are relevant but intentionally not run from a support-doc stress pass | `recursive_integration_trial_plan@1`, `recursive_integration_execution_record@1`, `rollback_readiness_record@1`, `integration_containment_report@1` | bounded trial/integration only, no constitutional self-amendment engine |
| `V73` | longitudinal outcome review and recursive improvement ledger | stale extractor and approximate test witness show tool usefulness can decay | `recursive_outcome_review@1`, `self_improvement_ledger@1`, `promotion_demotion_decision@1`, `tool_fitness_drift_register@1` | review and promotion/demotion recommendation only |
| `V74` | self-improvement operator studio / decision projection | clean tool exits need human-legible applicability context | `self_improvement_operator_case_view@1`, `ratification_workbench_projection@1`, `decision_visibility_contract@1` | projection of already typed authority only, no authority minted by UI |
| `V75` | governed dispatch, execute, and multi-worker widening | runtime widening should wait until candidate, evidence, ratification, containment, and review gates exist | `governed_dispatch_packet@1`, `execute_authority_lease@1`, `multi_worker_orchestration_topology@1`, `dispatch_reconciliation_report@1` | later execution widening only after recursive gates exist |

## Schema Seams Added By This Pass

These are not released schemas. They are support-layer schema targets for future
family planning.

`adeu_arc_namespace_map@1`:

- separates `selector_version`, `family_arc`, `implementation_arc`, `evidence_arc`,
  and `slice_id`;
- records whether a tool invocation uses one namespace while a reasoning claim uses
  another;
- requires an explicit join record before a closure claim can cross namespaces.

`arc_mapping_tool_applicability_report@1`:

- records tool name, invocation, intended claim, observed output schema, exit posture,
  applicability class, and map consequence;
- distinguishes `validates`, `constrains`, `not_applicable`, `stale_or_mismatched`,
  and `local_sanity_only`;
- forbids clean exit codes from being treated as broad conceptual proof unless the
  tool's schema actually covers that claim.

`tool_fitness_drift_register@1`:

- records tools whose historical fixture tests pass while live extraction no longer
  matches the current planning corpus;
- separates broken implementation from horizon-specific obsolescence;
- feeds `V73` outcome review rather than forcing every stale tool into the next arc.

## Hardened Proof Sketch

Sufficiency:

- `V68` answers "what graph, namespace, and evidence surface are we actually talking
  about?" and prevents selector/family/implementation arc laundering.
- `V69` turns candidate advancements into typed O/E/D/U records instead of prose
  opportunities.
- `V70` classifies the evidence burden and tool applicability before anyone treats a
  pass, warning, or empty record count as adoption evidence.
- `V71` keeps human-internal ratification and constitutional amendment authority
  explicit.
- `V72` supplies bounded trial, containment, and rollback before runtime mutation is
  widened.
- `V73` observes whether integrations and tools remain useful after use, including
  stale extractor drift.
- `V74` makes the whole case visible to the operator without letting UI placement
  mint authority.
- `V75` widens dispatch, execute, and multi-worker capability only after the previous
  gates exist.

Necessity:

- Without `V68`, the empirical run can pass `ARC=67` and still not validate family
  `V67`; namespace ambiguity remains live.
- Without `V69`, the map has no native way to admit an external or internal
  advancement as a recursive candidate.
- Without `V70`, advisory constitutional reports, approximate test selection, empty
  semantic blocks, and successful test runs can be over-read.
- Without `V71`, warning-only checks can be mistaken for constitutional gates or
  ratification.
- Without `V72`, running resident-runtime tools from a support-doc stress pass would
  collapse reasoning review into effectful experimentation.
- Without `V73`, stale or horizon-mismatched tools are discovered ad hoc and not
  reviewed as part of self-improvement outcome history.
- Without `V74`, the human operator sees scattered command results instead of one
  governed decision case.
- Without `V75`, execution remains narrow and manually orchestrated even after the
  recursive governance loop exists.

Minimality:

- No new ninth family is required for tool applicability. The tool-applicability
  seam belongs in `V68` when describing the graph and in `V70` when judging evidence.
- No new family is required for stale-tool handling. Drift registration belongs in
  `V73`, because usefulness over time is an outcome-review concern.
- No new family is required for coordinate emission. Coordinate records are a `V68`
  graph/cartography output, not a separate authority owner.
- No existing family can absorb the whole hardened `V68` seam. `V45-C` has historical
  dependency-register contracts, but the live extractor failed under the current
  planning corpus, so current full-series cartography needs a fresh family boundary.

The resulting family set is therefore still sufficient, necessary, and minimal at
family granularity, with sharper slice obligations inside `V68`, `V70`, and `V73`.

## Machine-Checkable Seed

```json
{
  "schema": "adeu_arc_series_multi_layer_mapping@1",
  "status": "support_synthesis_empirically_hardened_draft",
  "authority_layer": "support",
  "source_document": "docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v1.md",
  "predecessor_document": "docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v0.md",
  "source_selector_range": {
    "from": "docs/DRAFT_NEXT_ARC_OPTIONS_v2.md",
    "to": "docs/DRAFT_NEXT_ARC_OPTIONS_v52.md"
  },
  "current_closed_family_baseline": "V67",
  "namespace_layers_required": [
    "selector_version",
    "family_arc",
    "implementation_arc",
    "evidence_arc",
    "slice_id"
  ],
  "empirical_loop": {
    "schema": "arc_mapping_tool_applicability_report@1",
    "result_classes": [
      "validates",
      "constrains",
      "not_applicable",
      "stale_or_mismatched",
      "local_sanity_only"
    ],
    "tool_results": [
      {
        "tool": "make arc-closeout-check ARC=67",
        "observed_output_schemas": [
          "arc_bundle_lint@1",
          "closeout_consistency_lint@1",
          "semantic_compiler_closeout_lint@1"
        ],
        "exit_posture": "pass",
        "applicability_class": "constrains",
        "finding": "validates historical vNEXT_PLUS67 closeout posture, not family V67 closure"
      },
      {
        "tool": "lint_recursive_coordinate_warnings.py on v0",
        "observed_output_schemas": [
          "recursive_coordinate_warning_lint@1"
        ],
        "exit_posture": "pass_zero_records",
        "applicability_class": "not_applicable",
        "finding": "the map has no recursive_schema_coordinate@1 records"
      },
      {
        "tool": "adeu_semantic_source.compile_semantic_source on v0",
        "observed_output_schemas": [
          "semantic_source_compile_result"
        ],
        "exit_posture": "pass_zero_semantic_blocks",
        "applicability_class": "constrains",
        "finding": "the map is support prose, not ANM semantic-source material"
      },
      {
        "tool": "lint_constitutional_coherence_v55a.py",
        "observed_output_schemas": [
          "constitutional_coherence_report@1",
          "constitutional_unresolved_seam_register@1"
        ],
        "exit_posture": "pass_warning_only",
        "applicability_class": "constrains",
        "finding": "7 unresolved seed seams remain not_evaluable_yet"
      },
      {
        "tool": "lint_constitutional_coherence_v55c.py",
        "observed_output_schemas": [
          "constitutional_governance_calibration_register@1",
          "constitutional_migration_decision_register@1"
        ],
        "exit_posture": "pass_advisory_only",
        "applicability_class": "constrains",
        "finding": "constitutional migration remains advisory and warning-only"
      },
      {
        "tool": "adeu_repo_description.test_selection_v0",
        "observed_output_schemas": [
          "repo_test_selection_plan@2"
        ],
        "exit_posture": "pass_narrow_selection",
        "applicability_class": "constrains",
        "finding": "selected semantic compiler guards but lacks dedicated arc-map witness"
      },
      {
        "tool": "pytest packages/adeu_semantic_compiler/tests/test_semantic_compiler_guards.py",
        "observed_output_schemas": [
          "pytest_result"
        ],
        "exit_posture": "pass_35_tests_after_timeout_bound_rerun",
        "applicability_class": "validates",
        "finding": "semantic compiler guard tests pass; one unbounded rerun hung after printing completion and warning summary"
      },
      {
        "tool": "pytest packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_recursive_depth.py packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_models.py",
        "observed_output_schemas": [
          "pytest_result"
        ],
        "exit_posture": "pass_18_tests",
        "applicability_class": "validates",
        "finding": "released reasoning assessment model and recursive-depth tests are healthy but do not evaluate the arc-series map directly"
      },
      {
        "tool": "pytest packages/adeu_repo_description/tests/test_repo_description_v45c.py",
        "observed_output_schemas": [
          "pytest_result"
        ],
        "exit_posture": "pass_24_tests",
        "applicability_class": "validates",
        "finding": "repo arc dependency register schemas and historical fixtures validate"
      },
      {
        "tool": "derive_v45c_repo_arc_dependency_register",
        "observed_output_schemas": [
          "repo_arc_dependency_register@2"
        ],
        "exit_posture": "failure",
        "applicability_class": "stale_or_mismatched",
        "finding": "live extractor still expects V45-B broader selected branch marker"
      },
      {
        "tool": "local JSON block parser over v1",
        "observed_output_schemas": [
          "adeu_arc_series_multi_layer_mapping@1"
        ],
        "exit_posture": "pass_one_json_block_eight_families",
        "applicability_class": "local_sanity_only",
        "finding": "embedded v1 seed is syntactically valid JSON with eight family records"
      }
    ]
  },
  "minimal_missing_family_set": [
    {
      "family": "V68",
      "theme": "arc_cartography_namespace_tool_applicability_and_closure_registry",
      "empirical_drivers": [
        "arc_namespace_mismatch",
        "v45c_live_extractor_stale_or_horizon_mismatched",
        "recursive_coordinate_records_absent"
      ],
      "primary_outputs": [
        "adeu_arc_namespace_map@1",
        "adeu_arc_series_graph@1",
        "adeu_family_closure_register@1",
        "adeu_selector_lineage_report@1",
        "arc_mapping_tool_applicability_report@1",
        "recursive_coordinate_emission_plan@1"
      ],
      "boundary": "support_planning_graph_only_no_runtime_authority"
    },
    {
      "family": "V69",
      "theme": "recursive_candidate_advancement_intake_and_odeu_mapping",
      "primary_outputs": [
        "recursive_candidate_advancement_record@1",
        "recursive_odeu_mapping@1",
        "candidate_source_provenance_packet@1"
      ],
      "boundary": "describe_and_map_only_no_adoption_decision"
    },
    {
      "family": "V70",
      "theme": "integration_class_classifier_quality_threshold_and_tool_result_evaluator",
      "primary_outputs": [
        "recursive_integration_classification@1",
        "recursive_quality_threshold_report@1",
        "integration_risk_register@1",
        "tool_result_applicability_judgment@1"
      ],
      "boundary": "evaluate_evidence_and_class_but_cannot_ratify"
    },
    {
      "family": "V71",
      "theme": "amendment_ratification_and_human_internal_authority_kernel",
      "primary_outputs": [
        "recursive_ratification_request@1",
        "recursive_ratification_record@1",
        "amendment_scope_boundary@1",
        "human_role_authority_profile@1"
      ],
      "boundary": "decision_and_ratification_only_no_implementation"
    },
    {
      "family": "V72",
      "theme": "contained_trial_integration_and_rollback_harness",
      "primary_outputs": [
        "recursive_integration_trial_plan@1",
        "recursive_integration_execution_record@1",
        "rollback_readiness_record@1",
        "integration_containment_report@1"
      ],
      "boundary": "bounded_trial_and_integration_only_no_constitutional_self_amendment_engine"
    },
    {
      "family": "V73",
      "theme": "longitudinal_outcome_review_recursive_improvement_ledger_and_tool_fitness_drift",
      "primary_outputs": [
        "recursive_outcome_review@1",
        "self_improvement_ledger@1",
        "promotion_demotion_decision@1",
        "tool_fitness_drift_register@1"
      ],
      "boundary": "review_and_promotion_demotion_recommendation_only"
    },
    {
      "family": "V74",
      "theme": "self_improvement_operator_studio_and_decision_projection",
      "primary_outputs": [
        "self_improvement_operator_case_view@1",
        "ratification_workbench_projection@1",
        "decision_visibility_contract@1"
      ],
      "boundary": "projection_only_no_authority_minted_by_ui"
    },
    {
      "family": "V75",
      "theme": "governed_dispatch_execute_and_multi_worker_widening",
      "primary_outputs": [
        "governed_dispatch_packet@1",
        "execute_authority_lease@1",
        "multi_worker_orchestration_topology@1",
        "dispatch_reconciliation_report@1"
      ],
      "boundary": "execution_widening_only_after_recursive_gates_exist"
    }
  ],
  "ordering_rule": "do_not_select_dispatch_execute_or_multi_worker_widening_before_candidate_intake_evaluation_ratification_containment_review_and_operator_projection_exist",
  "proof_status": "support_layer_empirical_proof_sketch_not_formal_proof"
}
```
