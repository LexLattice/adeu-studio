# Draft ADEU Candidate Outcome Review V73B Implementation Mapping v0

Status: support note for the planned `V73-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V73-B`
should add outcome observations, regression tracking, and tool-fitness drift
after `V73-A` has shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v63.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_OUTCOME_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V73-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V73-B` becomes active, it should receive its own canonical starter trio
after `V73-A` is merged and lean-closed. It should consume released `V73-A`
entry, source-index, and boundary-guardrail rows.

## Candidate New Surfaces

`V73-B` should select:

- `repo_candidate_outcome_observation_record@1`
- `repo_outcome_regression_register@1`
- `repo_tool_fitness_drift_register@1`

These surfaces should extend `V73-A` rows rather than creating a parallel
outcome universe.

## Outcome Observation Record

The outcome observation record should record:

- `observation_ref`
- `candidate_ref`
- `entry_refs`
- `outcome_source_refs`
- `baseline_refs`
- `intervention_refs`
- `evaluation_refs`
- `outcome_observation_posture`
- `confidence_posture`
- `carried_forward_gap_refs`
- `regression_refs`
- `tool_fitness_refs`
- `non_promotion_guardrail_refs`
- `limitation_note`

Minimum outcome observation posture:

- `benefit_observed`
- `harm_observed`
- `neutral_or_no_material_change`
- `mixed_outcome_observed`
- `inconclusive_outcome`
- `outcome_blocked_by_missing_evidence`
- `outcome_deferred_to_future_family`

Minimum confidence posture:

- `high_with_bounded_evidence`
- `moderate_with_limitations`
- `low_or_inconclusive`
- `blocked_by_missing_baseline`
- `blocked_by_missing_evaluation`
- `blocked_by_unchecked_regression`
- `not_applicable`

Observation is not promotion, demotion, release, or product authority.

## Regression Register

The regression register should record:

- `regression_ref`
- `candidate_ref`
- `observation_refs`
- `regression_posture`
- `regression_surface_kind`
- `negative_control_refs`
- `blocking_for_recommendation`
- `limitation_note`

Minimum regression posture:

- `no_regression_observed`
- `regression_observed`
- `regression_risk_detected`
- `regression_unknown`
- `regression_not_applicable`

Minimum regression surface kind:

- `docs_regression`
- `schema_regression`
- `validator_regression`
- `fixture_regression`
- `test_regression`
- `workflow_regression`
- `tool_applicability_regression`
- `operator_cognition_regression`
- `unknown_or_unchecked_surface`

Regression absence must not be inferred from a positive observation unless the
evaluation horizon says the relevant surface was checked.

## Tool Fitness Drift Register

The tool-fitness drift register should record:

- `tool_fitness_ref`
- `candidate_ref`
- `observation_refs`
- `tool_id`
- `tool_target_claim_refs`
- `tool_target_horizon_refs`
- `target_namespace_kind`
- `prior_applicability_refs`
- `tool_fitness_posture`
- `observed_result_refs`
- `limitation_note`

Minimum tool-fitness posture:

- `tool_fit_confirmed`
- `tool_fit_limited`
- `tool_fit_stale`
- `tool_fit_misleading`
- `tool_fit_unchecked`
- `tool_fit_not_applicable`

Tool fitness applies only to the declared target horizon. It cannot become
global tool applicability.

Validation should enforce:

- if `regression_posture = no_regression_observed`, then evaluation refs must
  cover the `regression_surface_kind` or `negative_control_refs` must be
  non-empty;
- if `outcome_observation_posture = benefit_observed`, then baseline refs,
  intervention refs, evaluation refs, and non-promotion guardrail refs must all
  be non-empty, and blocking regression refs must be absent by checked horizon
  or carried forward;
- if `tool_fitness_posture` is `tool_fit_confirmed` or `tool_fit_misleading`,
  then `tool_target_horizon_refs`, `target_namespace_kind`,
  `prior_applicability_refs`, and `observed_result_refs` must be non-empty.

## Mandatory Reject Cases

`V73-B` should reject:

- observation row with unknown `V73-A` entry refs;
- observation row whose candidate differs from referenced entry rows;
- benefit observed with no baseline, intervention, and evaluation refs;
- benefit observed while blocking regression refs remain uncarried;
- no-regression posture with no checked horizon;
- tool fit confirmed with no observed result refs;
- tool fit confirmed without target horizon, target namespace, or prior
  applicability refs;
- tool fit claimed globally rather than target-bound;
- observation claiming promotion, demotion, adoption, release, product,
  runtime, or dispatch authority;
- regression register converted into implementation priority;
- tool drift register converted into global tool deprecation.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_outcome_observation_record_v204_reference.json`
- `repo_outcome_regression_register_v204_reference.json`
- `repo_tool_fitness_drift_register_v204_reference.json`
- `repo_candidate_outcome_v204_reject_unknown_entry_ref.json`
- `repo_candidate_outcome_v204_reject_candidate_mismatch.json`
- `repo_candidate_outcome_v204_reject_benefit_without_evaluation_refs.json`
- `repo_candidate_outcome_v204_reject_benefit_with_uncarried_regression.json`
- `repo_candidate_outcome_v204_reject_no_regression_without_checked_horizon.json`
- `repo_candidate_outcome_v204_reject_tool_fit_without_result_refs.json`
- `repo_candidate_outcome_v204_reject_tool_fit_without_target_horizon.json`
- `repo_candidate_outcome_v204_reject_global_tool_fitness_claim.json`
- `repo_candidate_outcome_v204_reject_observation_as_promotion.json`
- `repo_candidate_outcome_v204_reject_regression_as_implementation_priority.json`

The future `vNext+204` number is provisional until the active starter lock is
drafted.

## Closeout Expectation

`V73-B` should leave the repo with observation, regression, and tool-fitness
records over released `V73-A` entries. It should not leave the repo with
promotion, adoption, release, product, runtime, dispatch, or projection
authority.
