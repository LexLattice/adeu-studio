# Draft ADEU Candidate Review Classification V70B Implementation Mapping v0

Status: support note for the planned `V70-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V70-B`
should add adversarial review and conflict classification after `V70-A` has
shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V70-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V70-B` becomes active, it should receive its own canonical starter trio
after `V70-A` is merged and lean-closed. It should consume released `V70-A`
classification rows and add adversarial review structure without resolving the
review.

## Candidate New Surfaces

`V70-B` should select:

- `repo_candidate_adversarial_review_matrix@1`
- `repo_candidate_review_conflict_register@1`
- `repo_candidate_review_gap_scan@1`

These surfaces should extend `V70-A` row vocabulary rather than creating a
parallel review universe.

## Adversarial Review Matrix

The adversarial review matrix should record:

- `review_ref`
- `candidate_ref`
- `claim_ref`
- `classification_refs`
- `review_perspective`
- `review_source_refs`
- `odeu_lanes`
- `adversarial_review_posture`
- `review_limitation_note`

Minimum review perspectives:

- `supporting_review`
- `opposing_review`
- `authority_boundary_review`
- `negative_control_review`
- `model_output_comparison_review`
- `operator_pressure_review`
- `tool_applicability_review`

## Review Relation / Conflict Register

The relation register should record conflicts and complementarities. Conflict
rows may block later handoff; complementarity rows may shape `V71` without being
treated as conflicts.

The register should record:

- `conflict_ref`
- `candidate_ref`
- `claim_refs`
- `review_refs`
- `review_relation_kind`
- `conflict_kind`
- `conflict_posture`
- `blocking_for_handoff`
- `required_resolution_surface`
- `limitation_note`

Minimum review relation kinds:

- `conflict`
- `complementarity`
- `orthogonal`
- `duplicate`
- `unclear_relation`

Minimum conflict kinds:

- `evidence_conflict`
- `authority_boundary_conflict`
- `source_integrity_conflict`
- `model_output_divergence`
- `utility_tradeoff_conflict`
- `operator_pressure_conflict`
- `tool_applicability_conflict`

Minimum conflict posture:

- `blocking_for_v71`
- `non_blocking_but_carry_forward`
- `requires_more_evidence`
- `requires_human_review`
- `deferred_to_future_family`

## Review Gap Scan

The review gap scan should record:

- `gap_ref`
- `candidate_ref`
- `classification_refs`
- `gap_kind`
- `source_refs`
- `severity`
- `recommended_next_surface`
- `limitation_note`

Minimum gap kinds:

- `missing_adversarial_review`
- `missing_counterevidence`
- `single_source_overclaim`
- `stale_or_missing_source`
- `authority_boundary_unclassified`
- `model_output_without_negative_control`
- `product_wedge_without_v74_boundary`
- `v69_handoff_unclassified`
- `v70a_claim_unreviewed_by_adversarial_matrix`

## Mandatory Reject Cases

`V70-B` should reject:

- adversarial review row with no classification refs;
- adversarial review row whose candidate is absent from `V70-A`;
- `V70-A` claim classification with no adversarial review row and no explicit
  `not_required_for_this_claim` posture;
- model-output comparison review without opposing or negative-control posture;
- conflict row with no review refs;
- conflict row marked resolved by `V70-B`;
- complementarity row forced into a conflict posture;
- single-source overclaim omitted from gap scan;
- product wedge review without explicit `V74` boundary gap or future-family
  review posture;
- operator pressure review treated as authority;
- adversarial review converted into ratified decision;
- review gap converted into implementation priority;
- `V71`, `V72`, `V74`, or `V75` selected by conflict classification.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_adversarial_review_matrix_v195_reference.json`
- `repo_candidate_review_conflict_register_v195_reference.json`
- `repo_candidate_review_gap_scan_v195_reference.json`
- `repo_candidate_review_v195_reject_missing_classification_ref.json`
- `repo_candidate_review_v195_reject_v70a_claim_unreviewed.json`
- `repo_candidate_review_v195_reject_model_output_without_negative_control.json`
- `repo_candidate_review_v195_reject_conflict_marked_resolved.json`
- `repo_candidate_review_v195_reject_complementarity_as_conflict.json`
- `repo_candidate_review_v195_reject_single_source_overclaim_omitted.json`
- `repo_candidate_review_v195_reject_product_wedge_without_boundary.json`
- `repo_candidate_review_v195_reject_adversarial_review_as_ratification.json`

The future `vNext+195` number is provisional until the active starter lock is
drafted.

## Slice Closeout Expectation

`V70-B` should leave the repo with explicit adversarial review, conflict, and
complementarity rows. It should make relation posture visible, not settled.
`V71` remains responsible for any ratification review.
