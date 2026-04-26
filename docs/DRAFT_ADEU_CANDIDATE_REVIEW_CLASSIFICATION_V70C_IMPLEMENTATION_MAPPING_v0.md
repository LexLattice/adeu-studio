# Draft ADEU Candidate Review Classification V70C Implementation Mapping v0

Status: support note for the planned `V70-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V70-C`
should synthesize review classification and prepare pre-`V71` handoff after
`V70-A` and `V70-B` have shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70B_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V70-C` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V70-C` becomes active, it should receive its own canonical starter trio
after `V70-B` is merged and lean-closed. It should close the family only after
proving that review classification remains non-ratifying.

## Candidate New Surfaces

`V70-C` should select:

- `repo_candidate_review_classification_summary@1`
- `repo_candidate_pre_ratification_handoff@1`

These surfaces should summarize and hand off released `V70-A` / `V70-B` rows
without changing their authority posture.

## Classification Summary

The classification summary should record:

- `summary_ref`
- `candidate_ref`
- `classification_refs`
- `adversarial_review_refs`
- `conflict_refs`
- `gap_refs`
- `summary_posture`
- `handoff_readiness`
- `non_ratification_guardrail`
- `limitation_note`

Minimum summary posture:

- `classified_ready_for_later_review`
- `classified_needs_more_evidence`
- `classified_blocked_by_conflict`
- `classified_blocked_by_authority_boundary`
- `classified_deferred_to_future_family`
- `classified_rejected_out_of_scope`

`classified_ready_for_later_review` means ready for a later review surface. It
does not mean ratified.

## Pre-`V71` Handoff

The pre-ratification handoff should record:

- `handoff_ref`
- `candidate_ref`
- `handoff_target`
- `handoff_posture`
- `classification_refs`
- `adversarial_review_refs`
- `unresolved_gap_refs`
- `blocking_conflict_refs`
- `required_resolution_surface`
- `non_authority_guardrail`

Minimum handoff targets:

- `v71_ratification_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff posture:

- `ready_for_v71_review`
- `blocked_by_conflict`
- `blocked_by_evidence_gap`
- `blocked_by_authority_boundary`
- `deferred_to_future_family`
- `rejected_out_of_scope`

The handoff target may request `V71` review. It must not perform `V71`
ratification.

If unresolved gap refs or blocking conflict refs are non-empty, the summary
posture must not be `classified_ready_for_later_review`, and the handoff posture
must not be `ready_for_v71_review`. The row should use a blocked or deferred
posture while preserving the requested later review surface.

## Family Closeout Alignment

`V70-C` should emit a family closeout alignment artifact analogous to the `V68`
and `V69` family closeout records. The alignment should list:

- closed slices;
- emitted surfaces;
- unresolved gaps carried forward;
- candidates ready for later review;
- candidates blocked or deferred;
- non-authority guardrails;
- future families still unselected.

## Mandatory Reject Cases

`V70-C` should reject:

- classification summary with no classification refs;
- handoff row with no classification refs;
- handoff row that claims ratified decision;
- unresolved blocking conflict omitted from handoff;
- unresolved evidence gap omitted from summary;
- `v71_ratification_review` handoff without non-ratification guardrail;
- `ready_for_v71_review` handoff with unresolved blocking conflicts or gaps;
- `V72` integration selected by summary;
- `V74` product projection selected by summary;
- product wedge summarized as product authorization;
- review classification converted into implementation ticket;
- family closeout claiming candidate truth, adoption, release, or dispatch.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_review_classification_summary_v196_reference.json`
- `repo_candidate_pre_ratification_handoff_v196_reference.json`
- `repo_candidate_review_v196_reject_summary_without_classification_refs.json`
- `repo_candidate_review_v196_reject_handoff_as_ratification.json`
- `repo_candidate_review_v196_reject_unresolved_conflict_omitted.json`
- `repo_candidate_review_v196_reject_unresolved_gap_omitted.json`
- `repo_candidate_review_v196_reject_ready_handoff_with_blockers.json`
- `repo_candidate_review_v196_reject_v72_integration_selected.json`
- `repo_candidate_review_v196_reject_product_authorization.json`
- `repo_candidate_review_v196_reject_family_closeout_claims_adoption.json`

The future `vNext+196` number is provisional until the active starter lock is
drafted.

## Family Closeout Expectation

`V70-C` should leave the repo ready to draft `V71` with a typed set of classified
candidates and explicit unresolved review gaps. The closeout should make clear
that `V70` produced review-classification machinery, not ratified truth.
