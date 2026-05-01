# Architecture ADEU Reconciliation Arbiter Family v0

Status: architecture / decomposition record for planned `V76`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V76` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` review classification, closed `V71`
ratification review, closed `V72` contained integration review, closed `V73`
outcome review, closed `V74` operator projection, and closed `V75` dispatch
review.

## 1. Family Thesis

`V76` is the reconciliation / arbiter hardening family.

It should make projected or later-observed worker / model / review outputs
claim-addressable, relation-addressable, and dissent-preserving without
confusing reconciliation with truth, ratification, runtime execution, product
authorization, release authority, or recursive self-approval.

`V76` may say:

- this projected output slot exists and needs relation review;
- this observed output, if source-bound, bears on this bounded claim horizon;
- this relation is conflict, complementarity, duplicate, orthogonal,
  unclear, or single-output/no-relation;
- this relation requires arbiter review, adversarial review, later settlement,
  or future-family review;
- this dissent is present, searched absent, unsearched, unknown, warning-only,
  or blocking;
- this later handoff should go to runtime permission, product review, external
  branch review, outcome review, experiment review, or another family.

`V76` must not say:

- arbiter output is truth;
- worker output is truth;
- model output is benchmark truth or global model selection;
- majority agreement is correctness;
- relation mapping is settlement;
- reconciliation is ratification;
- product pressure has product authorization;
- runtime permission, command execution, worker assignment, dispatch, release,
  external contest participation, living-memory authority, or recursive policy
  amendment has occurred.

## 2. Relationship To `V68` Through `V75`

`V68` provides source / authority cartography and namespace disambiguation.

`V69` provides source-bound candidate identity and non-adoption guardrails.

`V70` provides claim, evidence, adversarial-review, conflict, complementarity,
gap, and pre-ratification substrate.

`V71` provides request, authority profile, settlement, ratification review,
dissent, amendment-scope, and post-ratification substrate.

`V72` provides containment, target-boundary, trial, effect, rollback, and
commit / PR / merge / release authority posture substrate.

`V73` provides outcome, regression, tool-fitness, self-improvement ledger,
operator-cognition signal, and recommendation substrate.

`V74` provides operator projection, typed case view, model-output comparison,
exception visibility, decision visibility contract, workbench projection, and
post-projection handoff substrate.

`V75` provides dispatch-review request, worker-role / assignment / IO /
tool-applicability planning, exception registers, projected worker-output
slots, relation rows, reconciliation contracts, post-dispatch-review handoffs,
and dispatch-review family closeout alignment.

`V76` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, ratification review as implementation, contained trial posture
as outcome success, outcome recommendation as self-approval, operator
projection as authority, or dispatch review as execution.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Claim map | Which output slot or output ref bears on which claim horizon? | Treating output presence as correctness |
| Relation register | What relation exists between outputs or claim treatments? | Treating relation kind as settlement |
| Dissent register | What dissent, warning, or coverage gap must be preserved? | Treating unsearched dissent as absence |
| Arbiter authority | Who or what may review a relation horizon later? | Treating arbiter role as truth authority |
| Settlement request | What review is requested over unresolved relation posture? | Treating request as ratification |
| Adversarial relation review | Which counter-read or negative control is needed? | Treating single-perspective review as enough |
| Gap scan | What source, relation, dissent, or authority gap remains? | Treating gaps as implementation priority |
| Summary / handoff | What later surface should receive the state? | Performing runtime, product, external, or release work inside `V76` |

## 4. ODEU Reconciliation Posture

Reconciliation and arbiter records should preserve ODEU lane information with
an `odeu_lanes` field where useful. The field should be a sorted, non-empty
list even when the row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

`V76` is ontological when it identifies output slots, claim horizons, relation
rows, and dissent rows. It is epistemic when it tracks evidence, source
coverage, relation confidence, adversarial review, and gaps. It is deontic
when it preserves non-truth, non-settlement, non-runtime, non-product, and
non-release boundaries. It is utility-bearing when it recommends the next
review surface.

## 5. Reconciliation Vocabulary

Minimum reconciliation source role:

- `v75_reconciliation_plan_source`
- `v75_relation_row_source`
- `v75_reconciliation_contract_source`
- `v75_post_dispatch_review_handoff_source`
- `v75_family_closeout_source`
- `combined_dogfood_source`
- `absence_marker`

Minimum output presence posture:

- `projected_not_observed`
- `observed_from_authorized_prior_run`
- `observed_from_support_artifact`
- `missing_expected_output`
- `not_applicable`

Minimum claim kind:

- `projected_output_slot_existence`
- `projected_relation_review_need`
- `observed_output_content_claim`
- `observed_model_output_claim`
- `support_artifact_output_claim`
- `relation_placeholder_claim`

`projected_not_observed` rows may map projected slot existence, projected
relation-review need, or relation placeholders. They must not map observed
output-content claims.

Projected relation rows may express placeholder, single-output,
missing-source, or later-review need posture. They must not imply an observed
output conflict unless an observed output source is present.

Minimum claim map posture:

- `mapped_for_reconciliation_review`
- `blocked_by_projected_not_observed`
- `blocked_by_missing_relation_source`
- `blocked_by_required_later_authority`
- `future_family_only`
- `rejected_out_of_scope`

Minimum blocker preservation law:

- if a source, relation, handoff, or gap carries product, runtime, release,
  external branch, dispatch-execution, or recursive-policy authority blockers,
  the blocker remains blocking or future-family-only until a later selected
  family handles it;
- `V76` may make blockers visible, but cannot convert them into arbiter
  readiness.

Minimum relation kind:

- `conflict`
- `complementarity`
- `duplicate`
- `orthogonal`
- `unclear_relation`
- `single_output_no_relation`

Minimum relation review posture:

- `visible_unsettled`
- `requires_arbiter_review`
- `requires_adversarial_review`
- `blocked_by_missing_source`
- `blocked_by_no_observed_output`
- `deferred_no_selection`

Minimum dissent presence posture:

- `dissent_present`
- `searched_none_found`
- `not_searched`
- `not_applicable`
- `unknown`

Minimum dissent carry-forward posture:

- `carried_for_later_review`
- `warning_only`
- `blocking_until_reviewed`
- `not_applicable`
- `deferred_no_selection`

## 6. Family Slices

`V76-A` should instantiate the starter map/register layer:

- `repo_reconciliation_claim_map@1`
- `repo_arbiter_relation_register@1`
- `repo_reconciliation_dissent_register@1`

`V76-B` should instantiate review hardening over the starter layer:

- `repo_arbiter_authority_profile@1`
- `repo_reconciliation_settlement_request@1`
- `repo_adversarial_relation_review@1`
- `repo_reconciliation_gap_scan@1`

`V76-C` should instantiate summary and closeout alignment:

- `repo_reconciliation_review_summary@1`
- `repo_post_reconciliation_handoff@1`
- `repo_reconciliation_family_closeout_alignment@1`

## 7. Negative Laws

- Claim mapping is not truth.
- Relation registration is not settlement.
- Arbiter review is not ratification.
- Arbiter output is not truth.
- Worker output is not truth.
- Model output is not benchmark truth.
- Majority agreement is not correctness.
- Dissent preservation is not failure by itself.
- Searched absence and unsearched absence are different states.
- Product pressure is not product authorization.
- Runtime pressure is not runtime permission.
- Dispatch-review substrate is not dispatch execution.
- A handoff is not later-family completion.

## 8. Package Boundary

The first implementation surface should remain in `packages/adeu_repo_description`
because `V76` is still repo-grounded review metadata. If a later slice tries to
become live command execution, runtime permissioning, worker dispatch, product
UI, external contest automation, release automation, or a queryable living
decision graph, that work should split rather than expanding repo-description
by implication.
