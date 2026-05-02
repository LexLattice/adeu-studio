# Draft ADEU Cross-Corpus Governance V81-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V81-A`.

Authority layer: support.

This note scopes the first `V81` slice. It is not an implementation lock. The
active starter authority should come from a future canonical `vNext+227`
starter trio if this slice is selected.

## Slice Intent

`V81-A` should create the starter schema / model / validator backbone for
source-bound cross-corpus governance review requests. It should admit corpus
governance pressure over released `V80-C` substrate, index concrete corpus
sources or absence rows, separate request recordability from eligibility, and
preserve non-ingestion guardrails.

It must not create corpus-boundary contracts, imported-substrate provenance
registers, authority gap registers, exception registers, summaries, handoffs,
corpus ingestion, connector activation, endpoint access, cross-corpus
adjudication execution, product authorization, release authority,
living-memory authority, recursive policy amendment, or `V82` selection.

## Selected Starter Surfaces

`V81-A` should select only:

- `repo_cross_corpus_governance_request@1`
- `repo_cross_corpus_source_index@1`
- `repo_cross_corpus_non_ingestion_guardrail@1`

Expected files:

- `packages/adeu_repo_description/src/adeu_repo_description/cross_corpus_governance.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/schema/repo_cross_corpus_governance_request.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_non_ingestion_guardrail.v1.json`
- `spec/repo_cross_corpus_governance_request.schema.json`
- `spec/repo_cross_corpus_source_index.schema.json`
- `spec/repo_cross_corpus_non_ingestion_guardrail.schema.json`
- `packages/adeu_repo_description/tests/test_cross_corpus_governance_v81a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus227/repo_cross_corpus_governance_request_v227_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus227/repo_cross_corpus_source_index_v227_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus227/repo_cross_corpus_non_ingestion_guardrail_v227_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus227/repo_cross_corpus_governance_v227_reject_*.json`

## Source Basis

The starter should consume concrete source rows for:

- released `V80-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_readiness_summary_v226_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_post_external_branch_review_handoff_v226_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_review_family_closeout_alignment_v226_reference.json`
- `V80` family closeout evidence:
  - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v226/evidence_inputs/v80_family_closeout_alignment_v226.json`
  - `artifacts/agent_harness/v226/evidence_inputs/v80c_external_branch_review_closeout_evidence_v226.json`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.json`

Support and roadmap docs can contextualize `V81-A`; they cannot be the only
eligibility sources. Missing expected corpus sources should be explicit
absence rows, not reconstructed from prose memory.

## Minimum Row Fields

`repo_cross_corpus_source_index@1` should include:

- `source_rows`
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `cross_corpus_source_role`
  - `source_horizon`
  - `limitation_note`

Minimum `cross_corpus_source_role` values:

- `v80_summary_source`
- `v80_handoff_source`
- `v80_closeout_source`
- `concrete_repo_local_corpus_source`
- `concrete_imported_corpus_source`
- `concrete_benchmark_result_source`
- `concrete_customer_corpus_source`
- `concrete_paper_design_repo_bundle_source`
- `synthetic_corpus_descriptor_source`
- `explicit_corpus_absence_marker`
- `explicit_authority_absence_marker`
- `dogfood_context`
- `roadmap_context`
- `support_process_context`
- `absence_marker`

`repo_cross_corpus_governance_request@1` should include:

- `request_rows`
  - `cross_corpus_governance_request_ref`
  - `candidate_ref`
  - `source_refs`
  - `v80_summary_refs`
  - `v80_handoff_refs`
  - `v80_closeout_refs`
  - `corpus_family_ref`
  - `corpus_horizon_kind`
  - `corpus_source_currentness`
  - `corpus_review_posture`
  - `requested_boundary_horizon`
  - `requested_provenance_horizon`
  - `required_authority_posture`
  - `required_privacy_posture`
  - `required_license_posture`
  - `required_connector_posture`
  - `guardrail_refs`
  - `corpus_ingestion_posture`
  - `connector_activation_posture`
  - `external_endpoint_access_posture`
  - `adjudication_execution_posture`
  - `odeu_lanes`
  - `limitation_note`

Minimum `corpus_review_posture` values:

- `request_recorded_boundary_only`
- `request_recorded_absence_only`
- `eligible_for_cross_corpus_governance_review`
- `blocked_by_missing_source`
- `blocked_by_missing_corpus_source`
- `blocked_by_missing_corpus_boundary`
- `blocked_by_missing_provenance`
- `blocked_by_missing_authority`
- `blocked_by_missing_privacy_authority`
- `blocked_by_missing_license_or_consent`
- `blocked_by_missing_customer_data_authority`
- `blocked_by_missing_connector_authority`
- `blocked_by_benchmark_truth_guardrail`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum `corpus_source_currentness` values:

- `current_concrete_source`
- `explicit_absence_marker`
- `historical_context_only`
- `stale_or_superseded`
- `unknown_needs_review`

`repo_cross_corpus_non_ingestion_guardrail@1` should include:

- `guardrail_rows`
  - `guardrail_ref`
  - `candidate_ref`
  - `source_refs`
  - `forbidden_data_actions`
  - `forbidden_connector_actions`
  - `forbidden_downstream_authority`
  - `required_later_authority_refs`
  - `non_ingestion_posture`
  - `non_connector_posture`
  - `limitation_note`

## Validation Requirements

`V81-A` should enforce:

- every request row references known source rows;
- every source row has concrete source posture or explicit absence posture;
- support / dogfood / roadmap context cannot be the only eligibility source;
- request recordability may cite released `V80-C` substrate plus either a
  concrete corpus source or an explicit absence row;
- eligible rows cite released `V80-C` substrate and a concrete corpus source
  with `corpus_source_currentness = current_concrete_source`;
- rows with only explicit absence sources must use
  `request_recorded_absence_only` or `blocked_by_missing_corpus_source`, not
  `eligible_for_cross_corpus_governance_review`;
- dogfood, roadmap, support, historical, stale, and unknown-currentness rows
  cannot make a request eligible;
- `customer_provided_corpus` rows require privacy, license, and authority
  posture;
- benchmark-result rows cannot claim benchmark truth;
- endpoint refs cannot become endpoint access permission;
- connector refs cannot become connector activation;
- product-pressure rows remain product-blocked or future-product-routed;
- external branch pressure remains external-authority-blocked or
  future-family-routed;
- future `V81-B` surfaces are represented through horizons and postures, not
  refs to non-existent rows;
- all reference rows carry no-ingestion, no-connector, no-endpoint-access, and
  no-adjudication-execution posture.

## Reference Fixture Intent

The first fixture should include:

- a self-evidencing workflow row recorded as boundary-only or blocked
  cross-corpus governance pressure, depending on whether a concrete corpus
  source exists;
- a typed-adjudication product-pressure row blocked by product authority;
- `V80-C` source rows;
- dogfood and roadmap rows marked context-only;
- explicit absence rows for missing corpus source or missing corpus authority;
- non-ingestion guardrails for each candidate;
- zero corpus-boundary, provenance, authority-gap, exception, summary,
  handoff, ingestion, connector, product, release, graph-memory, or `V82`
  rows.

## Mandatory Reject Fixtures

Reject fixtures should cover:

- no request source refs;
- source row lacking concrete source or absence posture;
- support-only eligibility;
- customer corpus without privacy/license/authority posture;
- benchmark result source marked benchmark truth;
- endpoint ref as access permission;
- connector ref as activation;
- external branch handoff as activation or ingestion authority;
- product pressure marked ready without product authority gap;
- `V81-B` refs embedded in starter rows;
- empty forbidden data actions;
- empty forbidden connector actions;
- empty forbidden downstream authority;
- corpus ingestion, customer data handling, endpoint access, connector
  activation, adjudication execution, product authorization, release,
  recursive policy amendment, or `V82` selection.

## Deferred Surfaces

Deferred to `V81-B`:

- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`

Deferred to `V81-C`:

- `repo_cross_corpus_governance_summary@1`
- `repo_post_cross_corpus_review_handoff@1`
- `repo_cross_corpus_governance_family_closeout_alignment@1`
