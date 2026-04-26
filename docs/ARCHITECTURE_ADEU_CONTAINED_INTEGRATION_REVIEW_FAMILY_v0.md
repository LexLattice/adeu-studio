# Architecture ADEU Contained Integration Review Family v0

Status: architecture / decomposition record for planned `V72`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V72` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` candidate review classification, and closed
`V71` candidate ratification review.

## 1. Family Thesis

`V72` is the contained integration-review family.

It should make the repo able to translate ratified, source-bound candidate
pressure into a bounded integration plan, trial record, rollback posture, and
commit / release authority boundary without confusing those records with actual
merge, release, product, runtime, or dispatch authority.

`V72` may say:

- this `V71-C` handoff is eligible for contained integration planning;
- this candidate is blocked from integration planning because dissent, gaps,
  scope limits, or future-family routing remain;
- this repository surface is the bounded target of a trial plan;
- this proposed change is permitted only as a contained trial;
- this effect surface must be inspected;
- this rollback condition must hold before later review;
- this candidate may be handed to `V73` for outcome review after contained
  integration review.

`V72` must not say:

- files may be edited outside an explicit active slice lock;
- a local write is accepted project truth;
- a PR may be opened automatically;
- a commit, merge, or release has occurred;
- a product surface is selected;
- runtime permission or dispatch is authorized;
- a candidate has become a constitutional or recursive policy amendment by
  passing a trial.

## 2. Relationship To `V68`, `V69`, `V70`, And `V71`

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
- derivation manifests and gap scans;
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
- request-scope boundaries;
- settlement records;
- ratification / rejection / deferral records;
- dissent register rows;
- amendment-scope boundaries;
- post-ratification handoff rows.

`V72` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, or ratification as implementation.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Handoff input | Which `V71-C` handoff is eligible for contained integration planning? | Treating deferred or future-family-routed rows as ready |
| Target boundary | Which repo surface may be considered? | Treating a broad package or glob as bounded evidence |
| Trial plan | What is the proposed contained trial? | Treating a plan as an applied change |
| Effect surface | What behavior, schema, docs, fixtures, tests, or process surfaces could be affected? | Treating local write reachability as accepted effect truth |
| Rollback readiness | How can the trial be reverted or contained? | Treating rollback prose as tested rollback evidence |
| Commit / release posture | What authority boundary applies after trial review? | Treating trial success as commit, merge, release, or product authority |
| Outcome handoff | What should `V73` review later? | Performing outcome review inside `V72` |

## 4. ODEU Integration Posture

Contained integration review should preserve ODEU lane information with an
`odeu_lanes` field. The field should be a sorted, non-empty list even when the
row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

Integration readiness is primarily deontic and utility-bearing. It may depend on
ontological candidate identity and epistemic review posture, but it cannot erase
those upstream constraints.

## 5. Integration Authority Vocabulary

Minimum integration posture:

- `eligible_for_containment_planning`
- `blocked_by_dissent`
- `blocked_by_evidence_gap`
- `blocked_by_scope_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum target boundary kind:

- `docs_support_surface`
- `schema_surface`
- `validator_surface`
- `fixture_surface`
- `test_surface`
- `workflow_surface`
- `package_surface`
- `no_target_boundary`

Minimum target resolution kind:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `bounded_package_surface_with_child_refs`
- `no_target_boundary`

Minimum `V72-A` required trial posture:

- `no_trial_selected_in_v72a`
- `dry_run_required_later`
- `local_trial_required_later`
- `trial_blocked_until_source_gap_resolved`
- `trial_blocked_until_dissent_resolved`
- `future_family_trial_only`

Minimum `V72-B` actual trial posture:

- `planned_not_executed`
- `dry_run_recorded`
- `local_trial_recorded`
- `trial_blocked`
- `trial_reverted`
- `trial_ready_for_outcome_review`

Minimum trial diff posture:

- `no_diff_recorded`
- `proposed_diff_recorded`
- `local_diff_observed`
- `diff_reverted`
- `diff_accepted_for_review_only`
- `diff_rejected`
- `diff_requires_later_authority`

Minimum rollback posture:

- `rollback_not_required_for_docs_only`
- `rollback_plan_required`
- `rollback_plan_present`
- `rollback_verified`
- `rollback_blocked`
- `rollback_not_applicable`

Minimum commit / PR / merge / release posture fields:

- `commit_intent_posture`
- `pr_posture`
- `merge_posture`
- `release_posture`
- `released_truth_posture`

Minimum values:

- `no_commit_intent`
- `commit_intent_requires_maintainer`
- `commit_intent_not_selected`
- `no_pr_update_authority`
- `pr_update_requires_maintainer`
- `pr_update_not_selected`
- `no_merge_authority`
- `merge_requires_maintainer`
- `merge_not_selected`
- `no_release_authority`
- `release_requires_later_lock`
- `release_not_selected`
- `released_truth_not_claimed`

These values are posture records. They are not automation commands.

## 6. Family Surfaces

Expected surfaces:

| Surface | Likely slice | Role |
|---|---|---|
| `repo_contained_integration_candidate_plan@1` | `V72-A` | source-bound plan rows over released `V71-C` ready handoffs |
| `repo_integration_target_boundary@1` | `V72-A` | target surface and scope boundaries for contained review |
| `repo_integration_non_release_guardrail@1` | `V72-A` | explicit non-release, non-product, non-runtime guardrail rows |
| `repo_contained_integration_trial_record@1` | `V72-B` | trial, dry-run, or blocked-trial records over a selected plan |
| `repo_integration_effect_surface_register@1` | `V72-B` | effect-surface rows for files, schemas, fixtures, tests, docs, and workflows |
| `repo_integration_rollback_readiness@1` | `V72-B` | rollback requirements and verification posture |
| `repo_commit_release_authority_posture@1` | `V72-C` | commit, PR, merge, release, and released-truth boundaries |
| `repo_post_integration_outcome_review_handoff@1` | `V72-C` | handoff rows to `V73` or future-family review without outcome review |
| `repo_contained_integration_family_closeout_alignment@1` | `V72-C` | family closeout alignment without selecting `V73` or release |

Names may be standardized before lock. If the `repo_*` namespace is retained,
the lock should say these are repo-description contained-integration-review
surfaces, not live write, merge, release, product, or dispatch artifacts.

## 7. Family Slices

### 7.1 `V72-A`

Contained integration planning starter.

Owns:

- source rows over released `V71-C` handoff, amendment scope, and family
  closeout alignment artifacts;
- candidate containment plan rows for `ready_for_v72_review` handoffs only;
- embedded `integration_source_rows` or equivalent source-register rows so
  target-boundary and guardrail refs resolve concretely;
- target boundary rows;
- non-release guardrail rows;
- conditional validation for eligible, blocked, and future-family-only plans;
- reject fixtures for product/future-family/deferred/dissent rows promoted to
  integration planning.

Does not own:

- trial execution;
- local writes;
- rollback verification;
- commit / merge / release posture;
- outcome review;
- product projection;
- dispatch widening.

### 7.2 `V72-B`

Contained trial and rollback-readiness record layer.

Owns:

- trial records over released `V72-A` plans;
- effect-surface registers;
- rollback-readiness rows;
- trial diff posture rows or fields distinguishing proposed, local,
  accepted-for-review, reverted, rejected, and later-authority-required diffs;
- negative controls proving dry-run, local trial, accepted diff, commit, merge,
  and release remain distinct.

Does not own:

- final commit / release decision;
- outcome review;
- product authorization;
- runtime permission;
- dispatch.

### 7.3 `V72-C`

Commit / release boundary and post-integration handoff.

Owns:

- commit / PR / merge / release authority posture rows;
- concrete maintainer / human authority refs where later authority is required;
- post-integration handoff rows to `V73`, future-family review, or deferral;
- family closeout evidence proving contained integration review remains
  non-release and non-productizing.

Does not own:

- `V73` outcome review;
- `V74` product projection;
- `V75` dispatch;
- actual release truth.

## 8. Negative Laws

`V72` must reject or refuse to represent as integration-ready:

- candidate absent from released `V71-C` handoff substrate;
- candidate whose `V71-C` handoff is not `ready_for_v72_review`;
- product wedge routed to `V72`;
- conceptual-diff candidate deferred with dissent treated as ready;
- target boundary expressed only as a broad glob or package without a bounded
  target;
- package target boundary without concrete child refs or explicit limitation;
- containment plan with no rollback posture;
- `V72-A` row that uses `V72-B` actual trial posture as if the trial already
  happened;
- trial record that claims commit, merge, release, product authorization,
  runtime permission, or dispatch;
- local trial row without active-lock/source evidence, target-boundary refs, and
  non-release guardrail refs;
- rollback row that treats unverified rollback prose as verified rollback;
- commit / PR / merge / release posture row that claims released truth or hides
  required human authority behind free text;
- post-integration handoff that performs `V73` outcome review.

## 9. Source Rows

`V72-A` should define explicit integration source rows so source absence remains
data rather than prose memory.

The preferred starter shape is to embed `integration_source_rows` inside
`repo_contained_integration_candidate_plan@1` and require target-boundary and
guardrail source refs to resolve through those rows. A separate
`repo_integration_source_register@1` can be introduced later only if the starter
payload becomes too large.

Minimum integration source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `source_horizon`
- `limitation_note`

Every plan row, target-boundary row, guardrail row, and handoff ref should
resolve through concrete source rows or explicit absence rows.

## 10. Expected Family Closeout

`V72` should close with a typed contained-integration substrate ready for `V73`
outcome review where applicable. It should not claim that any candidate has been
merged, released, productized, runtime-permitted, dispatched, or proven as a
recursive policy amendment.
