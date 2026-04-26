# Draft ADEU Candidate Review Classification V70A Implementation Mapping v0

Status: support note for the planned `V70-A` starter implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V70-A` slice should create a bounded evidence-classification schema and
validator backbone without turning review classification into ratification.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V70-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not the same thing as the active-slice canonical
starter bundle.

When `V70-A` is implemented, the expected active-slice starter bundle is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS194.md`
- `docs/ASSESSMENT_vNEXT_PLUS194_EDGES.md`

That future lock should select only the narrow starter slice described here.

## Carry Forward

- `docs/DRAFT_NEXT_ARC_OPTIONS_v60.md` as the current `V70` selector draft
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md` as
  the closed candidate-intake-family evidence input
- released `V69-C` pre-`V70` handoff fixtures as the first review input
- `docs/support/arc_series_mapping/V68_V69_COMBINED_DOGFOOD_TEST_v0.md` as
  support-layer evidence that V68/V69 compose without authority laundering
- released `V68` cartography surfaces as source and authority-layer precedent

If an expected carry-forward source is missing when the active lock is drafted,
the starter fixture should represent that absence with an explicit source row
and source-presence posture. It should not reconstruct review state from prose
memory.

## Starter Surfaces

Candidate new `V70-A` surfaces:

- `repo_candidate_evidence_classification_record@1`
- `repo_candidate_evidence_source_index@1`
- `repo_candidate_review_boundary_guardrail@1`

Those surfaces should remain bounded to:

- one explicit source set;
- one candidate review input register seeded from `V69-C`;
- one evidence source index;
- one claim classification register;
- one boundary guardrail register;
- one hand-curated reference fixture;
- reject fixtures for source-free evidence, embedded ratification, and authority
  laundering.

They should decide only:

- how evidence sources are represented;
- how candidate claims and claim horizons are represented;
- how ODEU review lanes are represented;
- how evidence classification posture is represented;
- how adversarial review need is marked but not executed;
- how non-ratification guardrails are represented.

They should keep out of scope:

- adversarial review matrix;
- conflict register;
- review gap scan;
- ratification;
- implementation scheduling;
- product workbench;
- dispatch or execution widening.

## Starter Source Binding

`V70-A` reference fixtures should carry at least:

- `review_id`
- `snapshot_id`
- `source_set_id`
- `coverage_horizon`
- `candidate_input_refs`
- `evidence_source_rows`
- `claim_rows`
- `claim_classification_rows`
- `boundary_guardrail_rows`
- `non_ratification_summary`

Evidence source rows should include:

- `evidence_source_ref`
- `candidate_ref`
- `source_ref`
- `source_kind`
- `authority_layer`
- `source_presence_posture`
- `evidence_kind`
- `claim_horizon`
- `limitation_note`

Minimum source presence posture:

- `present`
- `missing_expected_support_artifact`
- `not_uploaded_in_review_snapshot`
- `generated_later`
- `external_unavailable`

Claim rows should include:

- `claim_ref`
- `candidate_ref`
- `claim_horizon`
- `odeu_lanes`
- `claim_label`
- `claim_source_refs`
- `limitation_note`

Claim classification rows should include:

- `classification_ref`
- `candidate_ref`
- `claim_ref`
- `odeu_lanes`
- `claim_horizon`
- `evidence_classification`
- `evidence_source_refs`
- `adversarial_review_posture`
- `classification_note`

Boundary guardrail rows should include:

- `candidate_ref`
- `classification_refs`
- `forbidden_review_roles`
- `allowed_next_review_surfaces`
- `non_ratification_guardrail`

## Starter Validation Split

Local model validators should validate one payload only:

- schema shape;
- frozen enums;
- sorted unique row identities;
- no absolute repo paths;
- no free-text authority layers;
- no evidence source with empty singular `source_ref`;
- no classification row with a dangling `claim_ref`;
- no classification row with empty evidence source refs;
- no `source_missing_or_stale` or `insufficient_evidence` classification
  without an explicit absence or limitation evidence-source row;
- no unknown candidate refs;
- no `supports_review_claim` without evidence source refs;
- no `requires_adversarial_review` classification paired with
  `not_required_for_this_claim`;
- no model-output comparison candidate classified without required
  adversarial review or conflict posture;
- no `pre_ratification_readiness` row without a non-ratification guardrail.

Bundle validators should validate cross-artifact relationships:

- candidate refs come from released `V69` fixtures or explicit rejected-unknown
  input rows;
- evidence source rows point to concrete source refs or explicit source absence
  posture;
- claim rows reference known candidates and source refs;
- classification rows reference known claim rows;
- classification rows reference known evidence source rows;
- boundary guardrail rows reference known classification rows;
- no classification row emits truth, adoption, ratification, implementation,
  product, release, or dispatch authority.

## Starter Constants

Expected constants:

- `REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA = "repo_candidate_evidence_classification_record@1"`
- `REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA = "repo_candidate_evidence_source_index@1"`
- `REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA = "repo_candidate_review_boundary_guardrail@1"`

The repo-native field name should be `schema`, not `schema_id`.

## Mandatory Reject Cases

`V70-A` should reject:

- unadmitted candidate reviewed without rejected-unknown posture;
- evidence source row with empty `source_ref`;
- evidence source row whose source does not exist and has no source absence
  posture;
- classification row with a dangling `claim_ref`;
- source-missing or stale classification with empty `evidence_source_refs`;
- glob promoted to evidence source;
- V69 intake record treated as evidence of candidate truth;
- support doc marked as lock authority;
- claim classification marked as ratified decision;
- `supports_review_claim` treated as adoption;
- `pre_ratification_readiness` treated as `V71` ratification;
- `requires_adversarial_review` paired with
  `not_required_for_this_claim`;
- model-output comparison classified without adversarial review need;
- product wedge classified as product authorization;
- boundary guardrail missing forbidden review roles;
- implementation, release, or dispatch authority emitted by classification.

## First Reference Fixture Intent

The first reference fixture should be a post-`V69` seed, not a final exhaustive
candidate review catalog.

Required coverage:

- at least one candidate from the `V69-C` pre-`V70` handoff fixture;
- at least one source-bound evidence row from committed `V69` artifacts;
- at least one explicit claim row with non-empty `odeu_lanes`;
- at least one `requires_adversarial_review` classification;
- at least one `authority_boundary_blocked` or `not_evidence_for_claim`
  classification;
- no candidate ratified, adopted, integrated, released, productized, or
  dispatched.

Positive `pre_ratification_readiness` coverage should remain narrow in `V70-A`.
It is more naturally exercised in `V70-C` after adversarial review and gap-scan
surfaces exist.

Recommended first fixture names:

- `repo_candidate_evidence_classification_v194_reference.json`
- `repo_candidate_evidence_classification_v194_reject_unadmitted_candidate.json`
- `repo_candidate_evidence_classification_v194_reject_dangling_claim_ref.json`
- `repo_candidate_evidence_classification_v194_reject_glob_as_evidence.json`
- `repo_candidate_evidence_classification_v194_reject_source_missing_without_absence_row.json`
- `repo_candidate_evidence_classification_v194_reject_intake_as_truth.json`
- `repo_candidate_evidence_classification_v194_reject_classification_as_ratification.json`
- `repo_candidate_evidence_classification_v194_reject_required_adversarial_marked_not_required.json`
- `repo_candidate_evidence_classification_v194_reject_support_doc_as_lock_authority.json`
- `repo_candidate_evidence_classification_v194_reject_missing_boundary_guardrail.json`
- `repo_candidate_evidence_classification_v194_reject_product_authorization.json`
- `repo_candidate_evidence_classification_v194_reject_dispatch_authority.json`

Unknowns should be explicit. The starter should not fake review completeness.
