# Draft ADEU Recursive Candidate Intake V69A Implementation Mapping v0

Status: support note for the planned `V69-A` starter implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V69-A` slice should create a bounded recursive candidate-intake schema and
validator backbone without turning candidate admission into adoption.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md`
- `docs/ARCHITECTURE_ADEU_RECURSIVE_CANDIDATE_INTAKE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69C_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V69-A` support spec is part of the early `A` / `B` / `C` support-spec bundle
for joint review. It is not the same thing as the active-slice canonical starter
bundle.

When `V69-A` is implemented, the expected active-slice starter bundle is:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS191.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS191.md`
- `docs/ASSESSMENT_vNEXT_PLUS191_EDGES.md`

That future lock should select only the narrow starter slice described here.

## Carry Forward

- `docs/DRAFT_NEXT_ARC_OPTIONS_v56.md` as the immediate post-`V68` planning handoff
- `docs/DRAFT_NEXT_ARC_OPTIONS_v57.md` as the current `V69` selector draft
- `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md` as the closed
  cartography-family evidence input
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.md` as
  support-layer dogfood evidence
- `docs/support/arc_series_mapping/V69_PREFLIGHT_DOGFOOD_TEST_v0.json` as the
  machine-readable seed for the first reference fixture
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECURSIVE_CANDIDATE_INTAKE_V69_PLANNING_v0.md`
  as integrated support-layer review shaping evidence
- released `V68` repo-description surfaces as source and authority-layer precedent

## Starter Surfaces

Candidate new `V69-A` surfaces:

- `repo_recursive_candidate_intake_record@1`
- `repo_candidate_source_register@1`
- `repo_candidate_non_adoption_guardrail@1`

Those surfaces should remain bounded to:

- one explicit source set;
- one candidate register;
- one source register;
- one role / guardrail register;
- one hand-curated reference fixture seeded from the `V69` preflight dogfood report;
- reject fixtures for missing sources, missing guardrails, namespace collapse, and
  authority laundering.

They should decide only:

- how candidate rows are represented;
- how concrete source binding is represented;
- how source status and source presence are represented;
- how origin class, primary ODEU lane, and multi-lane ODEU pressure are represented;
- how admissible and forbidden roles are represented;
- how required next review surfaces are represented;
- how eventual family hints are represented without selecting later families;
- how non-adoption guardrails are represented.

They should keep:

- no automatic candidate derivation;
- no evidence classification;
- no adversarial review settlement;
- no ratification;
- no integration or release authority;
- no product workbench;
- no dispatch or execution widening.

## Starter Source Binding

`V69-A` reference fixtures should carry at least:

- `intake_id`
- `snapshot_id`
- `source_set_id`
- `coverage_horizon`
- `source_rows`
- `candidate_rows`
- `role_guardrail_rows`
- `non_adoption_summary`

Source rows should include:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `integration_note`

Candidate rows should include:

- `candidate_ref`
- `candidate_label`
- `origin_class`
- `intake_posture`
- `primary_odeu_lane`
- `odeu_lanes`
- `source_refs` (non-empty)
- `equivalence_posture`
- `intake_note`

Role / guardrail rows should include:

- `candidate_ref`
- `admissible_roles`
- `forbidden_roles`
- `required_next_review_surface`
- `eventual_family_hint`
- `non_adoption_guardrail`

The starter fixture should include the six candidates classified in
`V69_PREFLIGHT_DOGFOOD_TEST_v0.md` and should mark them as admitted for tracking,
not selected for adoption.

## Starter Validation Split

Local model validators should validate one payload only:

- schema shape;
- frozen enums;
- sorted unique row identities;
- no absolute repo paths;
- no free-text authority layers;
- no missing source-status posture;
- no missing non-adoption guardrail;
- no candidate with empty `source_refs`;
- no `source_refs` entry without a matching source row;
- no `primary_odeu_lane=mixed` when `odeu_lanes` is absent.

Bundle validators should validate cross-artifact relationships:

- candidate rows reference known source rows;
- role / guardrail rows reference known candidate rows;
- every `intake_candidate` row has a required next review surface;
- every admitted candidate has risk-aware forbidden roles based on origin class and
  admissible roles;
- duplicate candidates carry explicit equivalence posture;
- no candidate row claims lock, release, product, ratification, or dispatch
  authority.

## Starter Constants

Expected constants:

- `REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA = "repo_recursive_candidate_intake_record@1"`
- `REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA = "repo_candidate_source_register@1"`
- `REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA = "repo_candidate_non_adoption_guardrail@1"`

The repo-native field name should be `schema`, not `schema_id`.

## Mandatory Reject Cases

`V69-A` should reject:

- candidate row with empty `source_refs`;
- candidate `source_refs` that do not point to source rows;
- explicit source absence represented outside a source row;
- integrated source row whose `source_presence_posture` is not `present`;
- support doc marked as released schema;
- planning selector marked as lock authority;
- review feedback marked as ratified decision;
- transcript or operator turn marked as truth;
- operator-turn candidate without `transcript_truth` and `lock_authority` in
  `forbidden_roles`;
- model output marked as adopted candidate;
- model-output candidate without `ratified_decision` and `self_validation` in
  `forbidden_roles`;
- operator turn that invents a candidate without source binding;
- duplicate candidate without equivalence posture;
- candidate without `non_adoption_guardrail`;
- candidate whose forbidden roles omit all adoption / authority risks;
- schema candidate without `released_schema` in `forbidden_roles`;
- product-projection candidate without `product_authorization` in
  `forbidden_roles`;
- future-family candidate without `lock_authority` and `implementation_task` in
  `forbidden_roles`;
- `primary_odeu_lane=mixed` without non-empty `odeu_lanes`;
- `V70` evidence classification embedded inside intake;
- `V71` ratification embedded inside intake;
- `V72` commit / release authority embedded inside intake;
- `V74` product projection selected by intake;
- `V43` external-world contest branch selected by intake.

## First Reference Fixture Intent

The first reference fixture should be a post-`V68` seed, not a final exhaustive
candidate catalog.

Required coverage:

- `V69` planned / not started;
- `V69-A` selected as starter;
- `V69-B` and `V69-C` deferred until their own locks;
- `V70` tracked as immediate review target where needed;
- `V71` through `V75` and `V43` tracked only as eventual family hints or deferred
  targets;
- the six `V69` preflight dogfood candidates admitted for tracking;
- no candidate adopted, ratified, integrated, released, or selected for product.

Recommended first fixture names:

- `repo_recursive_candidate_intake_v191_reference.json`
- `repo_recursive_candidate_intake_v191_reject_missing_source_binding.json`
- `repo_recursive_candidate_intake_v191_reject_support_doc_as_released_schema.json`
- `repo_recursive_candidate_intake_v191_reject_selector_as_lock_authority.json`
- `repo_recursive_candidate_intake_v191_reject_review_feedback_as_ratification.json`
- `repo_recursive_candidate_intake_v191_reject_operator_turn_invents_unsourced_candidate.json`
- `repo_recursive_candidate_intake_v191_reject_duplicate_without_equivalence.json`
- `repo_recursive_candidate_intake_v191_reject_missing_non_adoption_guardrail.json`
- `repo_recursive_candidate_intake_v191_reject_embedded_v70_evidence_classification.json`
- `repo_recursive_candidate_intake_v191_reject_candidate_authorizes_v72_release.json`
- `repo_recursive_candidate_intake_v191_reject_product_projection_selected_by_intake.json`

Unknowns should be explicit. The starter should not fake candidate completeness.
