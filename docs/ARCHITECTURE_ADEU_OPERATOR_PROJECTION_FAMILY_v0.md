# Architecture ADEU Operator Projection Family v0

Status: architecture / decomposition record for planned `V74`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V74` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` candidate review classification, closed `V71`
candidate ratification review, closed `V72` contained integration review, and
closed `V73` candidate outcome review.

## 1. Family Thesis

`V74` is the operator projection and typed case-view family.

It should make the repo able to project source-bound candidate, review,
ratification, integration, outcome, recommendation, and exception state to a
human operator in a governed way, without confusing projection with authority.

`V74` may say:

- this candidate has a projection-ready operator case;
- these sources, recommendations, ledgers, signals, and exceptions are visible
  in the case;
- this case is an outcome-review case, typed-adjudication case,
  model-output-comparison case, product-pressure case, or future-family case;
- this visible status is blocked, ready for later review, deferred, or
  future-family-only;
- this operator action is only a review or visibility action;
- this decision requires later ratification, product, release, runtime,
  dispatch, or maintainer authority;
- this handoff may request a future family such as `V75` review.

`V74` must not say:

- a projection is a ratified decision;
- a case view is a source of truth by itself;
- visual prominence, operator click, transcript text, or dashboard state is
  authority;
- a product wedge is product authorization;
- a comparison projection proves a model is better;
- a recommendation has become adoption, release, dispatch, or self-approval;
- `V75` dispatch or multi-worker execution has already occurred.

## 2. Relationship To `V68` Through `V73`

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

`V73` provides outcome-review substrate:

- outcome-review entries;
- outcome evidence source rows and horizons;
- outcome observations;
- regression and tool-fitness drift rows;
- self-improvement outcome ledger rows;
- operator-cognition outcome signals;
- promotion / demotion / more-evidence recommendations;
- family closeout alignment rows.

`V74` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, ratification as implementation, contained trial posture as
outcome success, or outcome recommendation as operator authority.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Projection entry | Which source-bound state can be shown to the operator? | Treating a case view as a source of truth |
| Source visibility | Which sources, absences, blockers, and limitations must be visible? | Hiding missing or stale sources behind summary text |
| Typed case | What kind of case is this? | Collapsing outcome, model comparison, product pressure, and future-family pressure |
| Decision visibility | What state can the operator see? | Treating visibility as ratification, product selection, or execution |
| Workbench projection | Which later review actions can be requested? | Treating a button or projected action as authorization |
| Exception visibility | What blockers, dissent, regressions, or gaps remain? | Smoothing exceptions into confidence |
| Product projection | How should the typed-adjudication wedge be shown? | Treating product legibility as product authorization |
| Dispatch handoff | What can be carried toward later dispatch review? | Performing `V75` dispatch inside `V74` |

## 4. ODEU Projection Posture

Operator projection should preserve ODEU lane information with an `odeu_lanes`
field. The field should be a sorted, non-empty list even when the row is
single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

Projection is usually utility-bearing and deontic because it makes decisions
legible while preserving authority boundaries. It may also be epistemic when it
projects evidence status, and ontological when it projects candidate identity.

## 5. Projection Vocabulary

Minimum projection case kind:

- `self_improvement_outcome_case`
- `candidate_decision_case`
- `operator_cognition_signal_case`
- `typed_adjudication_case`
- `model_output_comparison_case`
- `product_pressure_case`
- `future_family_case`

Minimum projection posture:

- `eligible_for_operator_projection`
- `blocked_by_missing_source`
- `blocked_by_unresolved_regression`
- `blocked_by_unresolved_dissent`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum visible decision state:

- `ready_for_human_review`
- `blocked_pending_evidence`
- `blocked_pending_authority`
- `blocked_pending_dissent_resolution`
- `recommended_for_later_review`
- `recommended_more_evidence`
- `deferred_to_future_family`
- `rejected_out_of_scope`

Minimum projection horizon:

- `human_review_visibility`
- `later_ratification_review_request`
- `later_product_review_request`
- `later_dispatch_review_request`
- `future_family_visibility_only`

Minimum visible authority state:

- `no_authority_granted`
- `ratification_required`
- `product_authority_missing`
- `runtime_authority_missing`
- `dispatch_authority_missing`
- `release_authority_missing`

Minimum projection source role:

- `primary_projection_source`
- `outcome_ledger_source`
- `operator_signal_source`
- `recommendation_source`
- `family_closeout_source`
- `dogfood_source`
- `review_source`
- `ratification_source`
- `integration_source`
- `conceptual_diff_source`
- `product_wedge_source`
- `prompt_source`
- `model_output_source`
- `adjudicator_schema_source`
- `absence_marker`

Minimum visible blocker kind:

- `source_gap`
- `unresolved_regression`
- `unresolved_dissent`
- `authority_boundary_gap`
- `product_authority_gap`
- `runtime_authority_gap`
- `dispatch_authority_gap`
- `release_authority_gap`
- `model_output_provenance_gap`
- `comparison_axis_gap`

Minimum visible blocker posture:

- `blocking`
- `warning_only`
- `carried_forward`
- `not_applicable`
- `unknown_needs_review`

Minimum operator action posture:

- `inspect_only`
- `acknowledge_only`
- `request_later_review_only`
- `annotate_source_gap_only`
- `export_support_report_only`
- `no_operator_action_selected`

Minimum forbidden projection authority:

- `ratification_authority`
- `adoption_authority`
- `implementation_authority`
- `commit_release_authority`
- `merge_authority`
- `released_truth`
- `product_authorization`
- `runtime_permission`
- `dispatch_authority`
- `external_contest_authority`

Minimum required later authority:

- `human_ratification_required`
- `maintainer_release_authority_required`
- `product_authority_required`
- `runtime_authority_required`
- `dispatch_authority_required`
- `external_contest_authority_required`
- `none_selected_here`

## 6. Family Surfaces

`V74-A` should define the projection-entry backbone:

- `repo_operator_projection_case_view@1`
- `repo_operator_projection_source_index@1`
- `repo_operator_projection_non_authority_guardrail@1`

`V74-B` should define typed adjudication and comparison projection:

- `repo_typed_adjudication_case_view@1`
- `repo_model_output_comparison_projection@1`
- `repo_projection_exception_visibility_register@1`

`V74-C` should define visibility contracts and handoff posture:

- `repo_decision_visibility_contract@1`
- `repo_ratification_review_workbench_projection@1`
- `repo_post_projection_handoff@1`
- `repo_operator_projection_family_closeout_alignment@1`

## 7. Negative Laws

Projection is not authority.

Case-view rows are not source truth.

Operator clicks are not ratification, release, product, runtime, or dispatch
authority.

Transcript text is not truth unless bound by an admitted source row and later
authority.

Dashboard state is not a lock.

Product-pressure visibility is not product authorization.

Typed adjudication projection is not proof of model superiority.

Model-output comparison projection is not benchmark truth.

A projected recommendation is not adoption.

A projected exception cannot be hidden to simplify the case.

Missing sources must be represented as source rows or explicit absence posture,
not repaired with prose memory.

`V74` cannot perform `V75` dispatch.

## 8. Family Closeout Expectation

After `V74-C`, the repo should have a source-bound operator projection layer:

- case views over released outcome / recommendation substrate;
- typed adjudication and model-output comparison projections;
- visible exceptions and blockers;
- decision visibility contracts;
- ratification-review workbench projection rows;
- post-projection handoff rows;
- family closeout alignment.

The closeout should make the repo ready to consider `V75` dispatch and
multi-worker orchestration only as a later family. It should not claim that
dispatch, product authorization, release, runtime permission, or external
contest participation has occurred.
