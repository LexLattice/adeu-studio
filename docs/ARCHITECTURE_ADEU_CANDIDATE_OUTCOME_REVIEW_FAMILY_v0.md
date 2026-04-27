# Architecture ADEU Candidate Outcome Review Family v0

Status: architecture / decomposition record for planned `V73`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V73` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` candidate review classification, closed `V71`
candidate ratification review, and closed `V72` contained integration review.

## 1. Family Thesis

`V73` is the candidate outcome-review family.

It should make the repo able to inspect a contained trial / effect / rollback /
authority-posture record and say what outcome evidence exists, what outcome
cannot yet be judged, what regressed, what tool fitness changed, and what later
recommendation should be carried forward, without confusing outcome review with
adoption, release, product selection, runtime permission, dispatch, or
self-approval.

`V73` may say:

- this `V72-C` handoff is eligible for outcome-review entry;
- these baseline, intervention, and evaluation horizons are the relevant review
  horizon;
- this source is outcome evidence, not merely trial evidence or authority
  posture;
- this candidate appears beneficial, harmful, neutral, regressed, or
  inconclusive within a bounded horizon;
- this tool or review surface appears stale, useful, insufficient, or drifting;
- this operator-cognition / workflow-residue signal should be preserved for
  later projection;
- this candidate should be recommended for promotion, demotion, repeat,
  deferral, or future-family review.

`V73` must not say:

- a candidate is adopted as recursive policy;
- a commit, PR update, merge, or release is authorized;
- released truth has been created;
- a product surface is selected;
- runtime permission or dispatch is authorized;
- an outcome-success claim is proof of self-improvement without later
  ratification or projection;
- `V74` or `V75` has already been performed.

## 2. Relationship To `V68` Through `V72`

`V68` provides the map substrate:

- source rows and authority layers;
- family / slice / arc namespace disambiguation;
- support lineage;
- evidence surface indexing;
- tool applicability boundaries;
- coordinate posture.

`V69` provides candidate substrate:

- source-bound candidate rows;
- source registers and source absence posture;
- non-adoption guardrails;
- operator-ingress bindings;
- recursive workflow residue reports.

`V70` provides review substrate:

- evidence source index;
- claim and classification rows;
- adversarial review matrix;
- conflict / complementarity register;
- review gap scan;
- classification summary;
- pre-ratification handoff rows.

`V71` provides ratification substrate:

- ratification requests;
- authority profiles;
- settlement records;
- ratification / rejection / deferral records;
- dissent register rows;
- amendment-scope boundaries;
- post-ratification handoff rows.

`V72` provides contained integration substrate:

- containment plans;
- target boundaries;
- non-release guardrails;
- contained trial records;
- effect-surface registers;
- rollback readiness;
- commit / PR / merge / release authority posture;
- post-integration outcome-review handoff rows.

`V73` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, ratification as implementation, or contained trial posture as
outcome success.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Outcome entry | Which `V72-C` handoff is eligible for outcome review? | Treating blocked or future-family handoffs as outcome-ready |
| Evidence source | What source bears on outcome? | Treating trial existence, tool pass, or authority posture as outcome proof |
| Review horizon | What baseline / intervention / evaluation window is in scope? | Treating an unbounded history scan as evidence |
| Outcome observation | What changed and with what confidence? | Treating observation as adoption or release truth |
| Regression | What got worse or remains blocked? | Hiding gaps because one positive outcome exists |
| Tool fitness drift | Which tool or validation surface proved useful, stale, or misleading? | Treating a passing tool as globally applicable |
| Operator cognition | Did the workflow change operator / reviewer state in a way worth tracking? | Treating a transcript insight as authority |
| Recommendation | What should later families consider? | Performing promotion, product projection, or dispatch inside `V73` |

## 4. ODEU Outcome Posture

Outcome review should preserve ODEU lane information with an `odeu_lanes` field.
The field should be a sorted, non-empty list even when the row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

Outcome review is usually utility-bearing and epistemic. It may depend on
ontological candidate identity and deontic authority boundaries, but it cannot
erase either upstream constraint.

## 5. Outcome Vocabulary

Minimum outcome-entry posture:

- `eligible_for_outcome_review`
- `blocked_by_missing_trial_evidence`
- `blocked_by_rollback_gap`
- `blocked_by_effect_gap`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum outcome evidence kind:

- `baseline_evidence`
- `intervention_evidence`
- `evaluation_evidence`
- `trial_evidence`
- `effect_evidence`
- `rollback_evidence`
- `authority_posture_evidence`
- `dogfood_evidence`
- `operator_cognition_evidence`
- `tool_run_evidence`
- `absence_evidence`

Minimum outcome evidence role:

- `primary_outcome_evidence`
- `auxiliary_trial_context`
- `auxiliary_effect_context`
- `auxiliary_rollback_context`
- `authority_boundary_context`
- `absence_marker`

Minimum outcome horizon kind:

- `baseline`
- `intervention`
- `evaluation`

Minimum horizon coverage posture:

- `covered`
- `partially_covered`
- `missing_expected_source`
- `not_applicable`
- `future_family_only`

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

Minimum tool-fitness posture:

- `tool_fit_confirmed`
- `tool_fit_limited`
- `tool_fit_stale`
- `tool_fit_misleading`
- `tool_fit_unchecked`
- `tool_fit_not_applicable`

Minimum recommendation posture:

- `recommend_promote_for_later_review`
- `recommend_demote_or_revert_for_later_review`
- `recommend_repeat_trial`
- `recommend_more_evidence`
- `recommend_future_family_review`
- `recommend_no_action`
- `recommend_reject_out_of_scope`

Minimum required next surface:

- `v74_operator_projection_review`
- `v72_repeat_trial_review`
- `future_ratification_or_policy_review`
- `future_family_review`
- `deferred_no_selection`

Minimum required later authority:

- `human_ratification_required`
- `maintainer_release_authority_required`
- `product_authority_required`
- `dispatch_authority_required`
- `none_for_no_action`

These values are review / recommendation records. They are not adoption,
release, product, runtime, or dispatch commands.

## 6. Family Surfaces

Expected surfaces:

| Surface | Likely slice | Role |
|---|---|---|
| `repo_candidate_outcome_review_entry@1` | `V73-A` | entry rows over released `V72-C` outcome-review handoffs |
| `repo_outcome_evidence_source_index@1` | `V73-A` | baseline / intervention / evaluation / trial / effect / rollback / dogfood source rows |
| `repo_outcome_review_boundary_guardrail@1` | `V73-A` | non-promotion, non-release, non-product, non-runtime, non-dispatch boundaries |
| `repo_candidate_outcome_observation_record@1` | `V73-B` | outcome observation rows over selected review entries |
| `repo_outcome_regression_register@1` | `V73-B` | regression, blocker, and negative-control rows |
| `repo_tool_fitness_drift_register@1` | `V73-B` | tool applicability and drift rows after outcome review |
| `repo_self_improvement_outcome_ledger@1` | `V73-C` | longitudinal ledger across reviewed candidates and outcomes |
| `repo_operator_cognition_outcome_signal@1` | `V73-C` | operator / reviewer cognition outcome signals without transcript authority |
| `repo_outcome_promotion_demotion_recommendation@1` | `V73-C` | promotion, demotion, repeat, deferral, or future-review recommendations |
| `repo_outcome_review_family_closeout_alignment@1` | `V73-C` | family closeout alignment without selecting `V74` or `V75` |

Names may be standardized before lock. If the `repo_*` namespace is retained,
the lock should say these are repo-description outcome-review surfaces, not
release, product, runtime, or dispatch artifacts.

## 7. Family Slices

### 7.1 `V73-A`

Outcome-review entry starter.

Owns:

- source rows over released `V72-C` handoff, authority-posture, and family
  closeout alignment artifacts;
- outcome-review entry rows for `ready_for_v73_review` handoffs only;
- outcome evidence source index rows;
- baseline / intervention / evaluation horizon rows;
- boundary guardrails preserving non-promotion, non-release, non-product,
  non-runtime, and non-dispatch posture.

Does not own:

- outcome success classification;
- regression judgment;
- tool-fitness drift judgment;
- self-improvement ledger entries;
- promotion or demotion recommendation;
- product projection;
- dispatch widening.

### 7.2 `V73-B`

Outcome observation and drift lane.

Owns:

- outcome observation records over released `V73-A` entries;
- regression and blocker rows;
- tool-fitness drift rows;
- preservation of missing or inconclusive evidence;
- reject fixtures for outcome observation as promotion, release, or product
  authority.

Does not own:

- final promotion or demotion recommendation;
- self-improvement ledger closeout;
- operator-facing projection;
- release, runtime, or dispatch authority.

### 7.3 `V73-C`

Ledger, recommendation, and family closeout lane.

Owns:

- self-improvement outcome ledger rows;
- operator-cognition outcome signals;
- promotion / demotion / repeat / more-evidence recommendation rows;
- family closeout alignment;
- handoff pressure to `V74` or future-family review.

Does not own:

- final adoption or self-approval;
- product workbench implementation;
- dispatch or multi-worker widening;
- release or runtime authority.

## 8. Negative Laws

`V73` must reject:

- outcome review entry without released `V72-C` handoff refs;
- blocked or future-family `V72-C` handoff treated as outcome-ready;
- trial existence treated as outcome success;
- effect existence treated as benefit without evaluation horizon;
- rollback plan treated as rollback success when evidence is absent;
- tool pass treated as global tool fitness;
- operator transcript treated as authority;
- outcome observation treated as promotion / demotion decision;
- recommendation treated as adoption, release, product authorization, runtime
  permission, or dispatch;
- family closeout claiming `V74` or `V75` is already selected.

## 9. Closeout Posture

`V73` should close with typed outcome-review substrate ready for `V74`
operator/product projection review. It should not close by claiming that the
candidate is self-improved, adopted, released, productized, runtime-permitted,
or dispatchable.
