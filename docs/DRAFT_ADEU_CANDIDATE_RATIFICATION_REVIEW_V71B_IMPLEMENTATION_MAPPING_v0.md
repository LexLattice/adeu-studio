# Draft ADEU Candidate Ratification Review V71B Implementation Mapping v0

Status: support note for the planned `V71-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V71-B`
should add settlement and ratification records after `V71-A` has shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V71-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V71-B` becomes active, it should receive its own canonical starter trio
after `V71-A` is merged and lean-closed. It should consume released `V71-A`
request, authority-profile, and scope-boundary rows and add bounded settlement /
ratification records without creating implementation authority.

## Candidate New Surfaces

`V71-B` should select:

- `repo_candidate_ratification_record@1`
- `repo_review_settlement_record@1`
- `repo_ratification_dissent_register@1`

These surfaces should extend `V71-A` row vocabulary rather than creating a
parallel ratification universe.

## Ratification Record

The ratification record should record:

- `ratification_ref`
- `candidate_ref`
- `request_refs`
- `settlement_refs`
- `decision_posture`
- `ratification_horizon`
- `allowed_next_review_surface`
- `ratifying_authority_profile_refs`
- `dissent_refs`
- `amendment_scope_refs`
- `non_integration_guardrail`
- `limitation_note`

Minimum decision posture:

- `ratified`
- `rejected`
- `deferred`
- `out_of_scope`

Minimum allowed next review surface:

- `v72_contained_integration_review`
- `future_family_review`
- `deferred_no_selection`

## Review Settlement Record

The settlement record should record:

- `settlement_ref`
- `candidate_ref`
- `request_refs`
- `source_relation_refs`
- `relation_kind`
- `source_gap_refs`
- `settlement_posture`
- `review_signal_posture`
- `settlement_authority_profile_refs`
- `dissent_refs`
- `carried_forward_refs`
- `limitation_note`

Minimum settlement posture:

- `settled_for_candidate_horizon`
- `partially_settled_with_dissent`
- `blocked_by_unresolved_conflict`
- `blocked_by_unresolved_gap`
- `requires_more_evidence`
- `requires_human_review`
- `future_family_only`

Minimum relation kind:

- `conflict`
- `complementarity`
- `orthogonal`
- `duplicate`
- `unclear_relation`

Minimum review signal posture:

- `warning_only`
- `gating_blocker`
- `settlement_required`
- `evidence_required`
- `human_review_required`
- `future_family_only`

## Dissent Register

The dissent register should record:

- `dissent_ref`
- `candidate_ref`
- `request_refs`
- `settlement_refs`
- `dissent_source_refs`
- `dissent_posture`
- `dissent_search_posture`
- `dissent_summary`
- `carry_forward_required`
- `limitation_note`

Minimum dissent posture:

- `no_dissent_recorded`
- `dissent_carried_forward`
- `minority_review_preserved`
- `unresolved_blocker`
- `not_applicable`

Minimum dissent search posture:

- `searched_none_found`
- `not_searched`
- `not_applicable`
- `dissent_present`
- `unknown`

## Mandatory Reject Cases

`V71-B` should reject:

- ratification record with no request refs;
- ratification record whose request is absent from `V71-A`;
- ratification by an authority profile that is not ratification-authorized for
  that horizon;
- ratification record whose `ratification_horizon` is absent from any referenced
  authority profile's `allowed_ratification_horizons`;
- blocked request ratified without a settlement record;
- unresolved blocking conflict ratified as settled;
- unresolved blocking gap ratified without deferral or carry-forward;
- dissent row dropped when settlement says partial or unresolved;
- `no_dissent_recorded` treated as proof of absence without
  `searched_none_found`;
- product wedge ratified for integration review;
- ratification record converted into implementation ticket;
- ratification outcome authorizing merge, release, product, runtime, or
  dispatch;
- settlement row selecting `V72`, `V74`, or `V75` work directly.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_ratification_record_v198_reference.json`
- `repo_review_settlement_record_v198_reference.json`
- `repo_ratification_dissent_register_v198_reference.json`
- `repo_candidate_ratification_v198_reject_missing_request_ref.json`
- `repo_candidate_ratification_v198_reject_unauthorized_authority_profile.json`
- `repo_candidate_ratification_v198_reject_blocked_without_settlement.json`
- `repo_candidate_ratification_v198_reject_unresolved_gap_ratified.json`
- `repo_candidate_ratification_v198_reject_dissent_dropped.json`
- `repo_candidate_ratification_v198_reject_product_wedge_integration_review.json`
- `repo_candidate_ratification_v198_reject_ratification_as_implementation.json`
- `repo_candidate_ratification_v198_reject_release_authority.json`

The future `vNext+198` number is provisional until the active starter lock is
drafted.

## Slice Closeout Expectation

`V71-B` should leave the repo with explicit ratification, rejection, deferral,
settlement, and dissent rows. It may ratify a candidate for later review, but it
must not implement, integrate, release, productize, or dispatch that candidate.
