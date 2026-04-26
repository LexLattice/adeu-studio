# Draft ADEU Candidate Review Classification V70 Implementation Mapping v0

Status: support / implementation mapping record for planned `V70`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V70`
family into likely package, schema, validator, fixture, and evidence work so the
family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V70` should add candidate evidence and adversarial-review classification without
turning classification into:

- candidate adoption;
- truth settlement;
- ratification;
- implementation scheduling;
- contained integration;
- release authority;
- product projection;
- dispatch or execution widening.

The implementation target is a typed review-classification family that can
represent:

- candidate review input from `V69`;
- evidence source rows;
- claim registry rows;
- claim horizons;
- ODEU review lanes as sorted non-empty `odeu_lanes` lists;
- evidence classification posture;
- adversarial review posture;
- conflict and complementarity relation posture;
- review gaps;
- pre-ratification handoff.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded candidate review classification
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus194/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V70` still describes repo/corpus metadata
and review state. If a later slice tries to become a live adjudication runtime,
human review workbench, or product UI, that work should be split away instead of
expanding `adeu_repo_description` by implication.

The proposed `repo_*` schemas are repo-description review-classification
surfaces, not ARC challenge artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/candidate_review_classification.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_candidate_review_classification_v70a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected later implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/candidate_review_adversarial.py`
- `packages/adeu_repo_description/src/adeu_repo_description/candidate_review_handoff.py`
- `packages/adeu_repo_description/tests/test_candidate_review_classification_v70b.py`
- `packages/adeu_repo_description/tests/test_candidate_review_classification_v70c.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_candidate_evidence_classification_record.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_evidence_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_review_boundary_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_candidate_adversarial_review_matrix.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_review_conflict_register.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_review_gap_scan.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_review_classification_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_candidate_pre_ratification_handoff.v1.json`

Expected mirror schema files:

- `spec/repo_candidate_evidence_classification_record.schema.json`
- `spec/repo_candidate_evidence_source_index.schema.json`
- `spec/repo_candidate_review_boundary_guardrail.schema.json`
- `spec/repo_candidate_adversarial_review_matrix.schema.json`
- `spec/repo_candidate_review_conflict_register.schema.json`
- `spec/repo_candidate_review_gap_scan.schema.json`
- `spec/repo_candidate_review_classification_summary.schema.json`
- `spec/repo_candidate_pre_ratification_handoff.schema.json`

## 3. Candidate `V70` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_candidate_evidence_classification_record@1` | `V70-A` | top-level evidence classification record with candidate, claim, source, ODEU, and classification rows |
| `repo_candidate_evidence_source_index@1` | `V70-A` | concrete evidence-source refs with source posture, evidence kind, authority layer, and claim horizon |
| `repo_candidate_review_boundary_guardrail@1` | `V70-A` | explicit guardrails preventing evidence classification from becoming ratification or adoption |
| `repo_candidate_adversarial_review_matrix@1` | `V70-B` | adversarial review perspectives and counter-claim rows |
| `repo_candidate_review_conflict_register@1` | `V70-B` | conflict and complementarity rows over evidence and review perspectives |
| `repo_candidate_review_gap_scan@1` | `V70-B` | gaps for missing evidence, missing counterevidence, stale sources, and authority overclaims |
| `repo_candidate_review_classification_summary@1` | `V70-C` | bounded summary of classified candidates and unresolved review state |
| `repo_candidate_pre_ratification_handoff@1` | `V70-C` | pre-`V71` handoff rows without ratification |

`V70-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not need to derive every candidate review
row automatically.

## 4. Source Classes

The family should consume concrete source refs from:

- `V68` cartography family closeout:
  - `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v190/evidence_inputs/v68_family_closeout_alignment_v190.json`
- `V69` candidate-intake family closeout:
  - `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v193/evidence_inputs/v69_family_closeout_alignment_v193.json`
- `V69` candidate review handoff:
  - `artifacts/agent_harness/v193/evidence_inputs/v69c_recursive_candidate_intake_handoff_evidence_v193.json`
  - `apps/api/fixtures/repo_description/vnext_plus193/repo_candidate_intake_pre_v70_handoff_v193_reference.json`
- support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become evidence-source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source or evidence-source row. The
review fixture should not reconstruct candidate handoff or evidence state from
planning prose.

## 5. Required Starter Enumerations

Source presence posture:

- `present`
- `missing_expected_support_artifact`
- `not_uploaded_in_review_snapshot`
- `generated_later`
- `external_unavailable`

Claim horizon:

- `source_existence`
- `candidate_well_formedness`
- `evidence_support`
- `authority_boundary`
- `adversarial_review_need`
- `conflict_presence`
- `pre_ratification_readiness`
- `utility_projection`

`pre_ratification_readiness` should be treated as a later-family review
readiness horizon, not a ratification result. Positive starter coverage should
favor source binding, authority boundary, evidence support, and adversarial
review need; broad positive readiness belongs more naturally in `V70-C`.

Evidence classification:

- `source_bound_for_review`
- `supports_review_claim`
- `contradicts_review_claim`
- `insufficient_evidence`
- `not_evidence_for_claim`
- `requires_adversarial_review`
- `authority_boundary_blocked`
- `tool_applicability_unknown`
- `source_missing_or_stale`

Adversarial review posture:

- `not_required_for_this_claim`
- `required_not_started`
- `required_present`
- `required_inconclusive`
- `conflict_detected`
- `blocked_missing_counterevidence`
- `deferred_to_future_family_review`

Review relation kind:

- `conflict`
- `complementarity`
- `orthogonal`
- `duplicate`
- `unclear_relation`

Review handoff target:

- `v71_ratification_review`
- `future_family_review`
- `deferred_no_selection`

Review handoff posture:

- `ready_for_v71_review`
- `blocked_by_conflict`
- `blocked_by_evidence_gap`
- `blocked_by_authority_boundary`
- `deferred_to_future_family`
- `rejected_out_of_scope`

Forbidden review role:

- `truth_verdict`
- `ratified_decision`
- `candidate_adoption`
- `implementation_task`
- `commit_release_authority`
- `product_authorization`
- `dispatch_authority`
- `self_validation`

## 6. Shared Row Vocabulary

Minimum evidence source row fields:

- `evidence_source_ref`
- `candidate_ref`
- `source_ref`
- `source_kind`
- `authority_layer`
- `source_presence_posture`
- `evidence_kind`
- `claim_horizon`
- `limitation_note`

Minimum claim row fields:

- `claim_ref`
- `candidate_ref`
- `claim_horizon`
- `odeu_lanes`
- `claim_label`
- `claim_source_refs`
- `limitation_note`

Minimum claim classification row fields:

- `classification_ref`
- `candidate_ref`
- `claim_ref`
- `odeu_lanes`
- `claim_horizon`
- `evidence_classification`
- `evidence_source_refs`
- `adversarial_review_posture`
- `classification_note`

Minimum boundary guardrail row fields:

- `candidate_ref`
- `classification_refs`
- `forbidden_review_roles`
- `allowed_next_review_surfaces`
- `non_ratification_guardrail`

Minimum adversarial review row fields:

- `review_ref`
- `candidate_ref`
- `claim_ref`
- `review_perspective`
- `review_source_refs`
- `adversarial_review_posture`
- `limitation_note`

Minimum conflict row fields:

- `conflict_ref`
- `candidate_ref`
- `claim_refs`
- `review_relation_kind`
- `conflict_kind`
- `conflict_posture`
- `blocking_for_handoff`
- `required_resolution_surface`

Minimum pre-ratification handoff row fields:

- `handoff_ref`
- `candidate_ref`
- `handoff_target`
- `handoff_posture`
- `classification_refs`
- `adversarial_review_refs`
- `unresolved_gap_refs`
- `non_authority_guardrail`

## 7. Mandatory Family Reject Themes

`V70` should reject:

- unadmitted candidate treated as review target;
- classification row with a dangling `claim_ref`;
- evidence-source row with empty or unknown singular `source_ref`;
- source-missing or stale classification without an explicit absence-posture
  evidence-source row;
- glob promoted to evidence;
- V69 intake treated as evidence of truth;
- support doc treated as lock authority;
- evidence classification treated as ratification;
- `requires_adversarial_review` paired with
  `not_required_for_this_claim`;
- adversarial review treated as settlement;
- conflict row silently resolved by classification;
- complementarity dropped because a register only accepts conflicts;
- handoff target that jumps to implementation, product, release, or dispatch;
- handoff with unresolved blocking conflicts or gaps marked
  `ready_for_v71_review`;
- pre-ratification handoff that claims ratified decision.

## 8. Family Closeout Expectation

After `V70-A/B/C`, the repo should have typed, source-bound, non-ratifying review
classification records that make `V71` ratification review possible. `V70`
should close with unresolved evidence and review conflicts carried forward rather
than repaired into apparent settlement.
