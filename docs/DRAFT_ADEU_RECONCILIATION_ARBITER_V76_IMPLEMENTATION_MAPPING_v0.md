# Draft ADEU Reconciliation Arbiter V76 Implementation Mapping v0

Status: support / implementation mapping record for planned `V76`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V76` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v66.md`
- `docs/ARCHITECTURE_ADEU_RECONCILIATION_ARBITER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_RECONCILIATION_ARBITER_V76_PLANNING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V76` should add reconciliation / arbiter hardening records without turning
them into:

- arbiter output as truth;
- worker output as truth;
- model output as benchmark truth or global model selection;
- majority agreement as correctness;
- relation settlement or ratification;
- worker assignment or dispatch execution;
- command execution or runtime permission;
- PR, commit, merge, release, or released truth;
- product authorization;
- external contest participation;
- living-memory authority;
- recursive policy amendment.

The implementation target is a typed reconciliation family that can represent:

- source-bound claim maps over released `V75-C` reconciliation plans and output
  slots;
- relation registers over released `V75-C` relation rows;
- dissent and search-coverage posture;
- arbiter authority profiles for later review;
- settlement requests without settlement;
- adversarial relation review and relation gap scans;
- summary and post-reconciliation handoff rows without later-family authority.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded reconciliation / arbiter records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus212/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V76` still describes repo/corpus
metadata and review posture. If a later family becomes live execution,
product UI, external automation, release automation, or graph query runtime,
that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/reconciliation_arbiter.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_reconciliation_arbiter_v76a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_reconciliation_claim_map.v1.json`
- `packages/adeu_repo_description/schema/repo_arbiter_relation_register.v1.json`
- `packages/adeu_repo_description/schema/repo_reconciliation_dissent_register.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_arbiter_authority_profile.v1.json`
- `packages/adeu_repo_description/schema/repo_reconciliation_settlement_request.v1.json`
- `packages/adeu_repo_description/schema/repo_adversarial_relation_review.v1.json`
- `packages/adeu_repo_description/schema/repo_reconciliation_gap_scan.v1.json`
- `packages/adeu_repo_description/schema/repo_reconciliation_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_reconciliation_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_reconciliation_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_reconciliation_claim_map.schema.json`
- `spec/repo_arbiter_relation_register.schema.json`
- `spec/repo_reconciliation_dissent_register.schema.json`
- `spec/repo_arbiter_authority_profile.schema.json`
- `spec/repo_reconciliation_settlement_request.schema.json`
- `spec/repo_adversarial_relation_review.schema.json`
- `spec/repo_reconciliation_gap_scan.schema.json`
- `spec/repo_reconciliation_review_summary.schema.json`
- `spec/repo_post_reconciliation_handoff.schema.json`
- `spec/repo_reconciliation_family_closeout_alignment.schema.json`

## 3. Candidate `V76` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_reconciliation_claim_map@1` | `V76-A` | top-level claim horizon map over released `V75-C` reconciliation plans and output slots |
| `repo_arbiter_relation_register@1` | `V76-A` | relation rows, relation review posture, arbiter need posture, and non-truth guardrails |
| `repo_reconciliation_dissent_register@1` | `V76-A` | dissent, warning, searched absence, unknown coverage, and carry-forward posture |
| `repo_arbiter_authority_profile@1` | `V76-B` | authority profile for who or what may review a relation horizon later |
| `repo_reconciliation_settlement_request@1` | `V76-B` | settlement request rows without settlement or ratification |
| `repo_adversarial_relation_review@1` | `V76-B` | adversarial relation review rows over claim maps and relation registers |
| `repo_reconciliation_gap_scan@1` | `V76-B` | source, relation, dissent, authority, and coverage gap scan |
| `repo_reconciliation_review_summary@1` | `V76-C` | synthesis of A/B rows without truth or ratification |
| `repo_post_reconciliation_handoff@1` | `V76-C` | later-review handoff after reconciliation review |
| `repo_reconciliation_family_closeout_alignment@1` | `V76-C` | family closeout alignment without runtime, product, external, release, or recursive authority |

`V76-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement arbiter authority,
settlement, runtime permission, dispatch, product workbenching, or release
authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V75` dispatch review family closeout:
  - `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v211/evidence_inputs/v75_family_closeout_alignment_v211.json`
  - `artifacts/agent_harness/v211/evidence_inputs/v75c_dispatch_review_closeout_evidence_v211.json`
- `V75-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus211/repo_worker_output_reconciliation_plan_v211_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_reconciliation_contract_v211_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus211/repo_post_dispatch_review_handoff_v211_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus211/repo_dispatch_review_family_closeout_alignment_v211_reference.json`
- support lineage:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
  - `docs/support/arc_series_mapping/REVIEW_GPTPRO_POST_V74_MULTI_ARC_ROADMAP_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become reconciliation source rows.

If any expected source is missing when an active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct reconciliation state from planning prose.

## 5. Shared Row Vocabulary

Minimum reconciliation source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `reconciliation_source_role`
- `source_horizon`
- `limitation_note`

Minimum claim map row fields:

- `claim_map_ref`
- `candidate_ref`
- `output_claim_ref`
- `claim_kind`
- `claim_label`
- `reconciliation_plan_refs`
- `projected_output_slot_refs`
- `observed_worker_output_refs`
- `v75_source_relation_refs`
- `handoff_refs`
- `claim_horizon`
- `claim_source_refs`
- `claim_presence_posture`
- `output_presence_posture`
- `claim_map_posture`
- `source_refs`
- `truth_status_forbidden`
- `non_truth_guardrail`
- `limitation_note`

Minimum claim kind:

- `projected_output_slot_existence`
- `projected_relation_review_need`
- `observed_output_content_claim`
- `observed_model_output_claim`
- `support_artifact_output_claim`
- `relation_placeholder_claim`

If `output_presence_posture = projected_not_observed`, then
`observed_worker_output_refs` must be empty and `claim_kind` must be one of
`projected_output_slot_existence`, `projected_relation_review_need`, or
`relation_placeholder_claim`.

If source or handoff material carries product, runtime, release, external
branch, dispatch-execution, or recursive-policy authority blockers,
`claim_map_posture` must remain blocked or future-family-only unless the
required next review surface preserves the blocker for that later family.

Minimum relation register row fields:

- `arbiter_relation_ref`
- `claim_map_refs`
- `source_relation_refs`
- `relation_kind`
- `relation_review_posture`
- `arbiter_need_posture`
- `required_next_review_surface`
- `source_refs`
- `non_truth_guardrail`
- `limitation_note`

Minimum dissent register row fields:

- `dissent_ref`
- `claim_map_refs`
- `relation_refs`
- `dissent_kind`
- `dissent_presence_posture`
- `dissent_search_horizon_refs`
- `dissent_search_coverage_posture`
- `checked_source_refs`
- `unchecked_source_refs`
- `dissent_source_refs`
- `dissent_carry_forward_posture`
- `limitation_note`

## 6. Validation Themes

Expected validators should enforce:

- source rows are explicit and concrete, or carry explicit absence posture;
- claim maps consume released `V75-C` reconciliation plans and relation rows
  through `v75_source_relation_refs`;
- projected output slots cannot become observed worker output refs;
- projected output slots cannot become observed output-content claims;
- observed worker output refs require authorized prior-run or support-artifact
  source posture;
- relation register rows remain non-truth and cannot settle claims;
- dissent rows preserve searched absence, unsearched absence, unknown, warning,
  and blocker states;
- `searched_none_found` dissent rows require explicit search horizon and checked
  source refs;
- product, runtime, release, external branch, dispatch-execution, and
  recursive-policy blockers remain visible;
- `V76-A` cannot emit `V76-B` or `V76-C` surfaces;
- no row creates arbiter truth, worker-output truth, settlement,
  ratification, worker assignment, dispatch execution, command execution,
  runtime permission, product authorization, external contest participation,
  PR creation, commit, merge, release, benchmark truth, model selection,
  living-memory authority, or recursive policy amendment.

## 7. Fixture Plan

First reference fixture should include:

- one self-evidencing workflow-type emergence trace where `V75-C` projected
  output and single-output relation rows are mapped for later reconciliation
  review;
- one typed-adjudication product wedge trace where product authority blockers
  remain visible and block readiness;
- one dissent / searched-absence row showing that absence and unknown coverage
  are not the same;
- zero settlement, ratification, execution, product, release, or runtime
  authority rows.

Reject fixtures should cover:

- source-free claim map;
- projected output treated as observed output;
- projected output slot mapped as observed content claim;
- observed worker output without authorized source posture;
- relation row claiming truth or settlement;
- dissent absence without searched horizon;
- authority blocker converted into arbiter readiness;
- model-output comparison converted into benchmark truth;
- `V76-A` emitting later-slice surfaces.

## 8. Verification Expectation

Docs-only starter bundles should use:

- `make arc-start-check ARC=<n>`

Python implementation PRs should use:

- focused `V76-A` tests plus export-schema tests during development;
- `make check` before PR creation or update.
