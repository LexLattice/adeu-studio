# Draft ADEU Corpus Ingestion Authority Review V82-A Implementation Mapping v0

Status: support / slice implementation mapping for planned `V82-A`.

Authority layer: support.

This note scopes the first `V82` slice. It is not an implementation lock. The
active starter authority should come from a future canonical `vNext+230`
starter trio if this slice is selected.

## Slice Intent

`V82-A` should create the starter schema / model / validator backbone for
source-bound corpus-ingestion review requests. It should admit ingestion review
pressure over released `V81-C` substrate, index concrete corpus / privacy /
license / connector / endpoint sources or absence rows, separate request
recordability from eligibility, and preserve non-transfer guardrails.

It must not create ingestion preflight contracts, connector access review
boundaries, data-handling authority review rows, exception registers,
summaries, handoffs, corpus ingestion, data transfer, customer data handling,
connector activation, endpoint access, cross-corpus adjudication execution,
product authorization, release authority, living-memory authority, recursive
policy amendment, or `V83` selection.

## Selected Starter Surfaces

`V82-A` should select only:

- `repo_corpus_ingestion_review_request@1`
- `repo_corpus_ingestion_source_index@1`
- `repo_corpus_ingestion_non_transfer_guardrail@1`

Expected files:

- `packages/adeu_repo_description/src/adeu_repo_description/corpus_ingestion_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_non_transfer_guardrail.v1.json`
- `spec/repo_corpus_ingestion_review_request.schema.json`
- `spec/repo_corpus_ingestion_source_index.schema.json`
- `spec/repo_corpus_ingestion_non_transfer_guardrail.schema.json`
- `packages/adeu_repo_description/tests/test_corpus_ingestion_review_v82a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`
- `apps/api/fixtures/repo_description/vnext_plus230/repo_corpus_ingestion_review_request_v230_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus230/repo_corpus_ingestion_source_index_v230_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus230/repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus230/repo_corpus_ingestion_v230_reject_*.json`

## Source Basis

The starter should consume concrete source rows for:

- released `V81-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_summary_v229_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_post_cross_corpus_review_handoff_v229_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json`
- `V81` family closeout evidence:
  - `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v229/evidence_inputs/v81_family_closeout_alignment_v229.json`
  - `artifacts/agent_harness/v229/evidence_inputs/v81c_cross_corpus_governance_closeout_evidence_v229.json`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.json`

Support and roadmap docs can contextualize `V82-A`; they cannot be the only
eligibility sources. Missing expected corpus, privacy, license, customer,
connector, endpoint, or transfer authority sources should be explicit absence
rows, not reconstructed from prose memory.

## Minimum Row Fields

`repo_corpus_ingestion_source_index@1` should include:

- `source_rows`
  - `source_ref`
  - `source_kind`
  - `authority_layer`
  - `source_status`
  - `source_presence_posture`
  - `ingestion_source_role`
  - `source_horizon`
  - `source_currentness`
  - `source_content_horizon`
  - `source_permission_posture`
  - `limitation_note`

Minimum `ingestion_source_role` values:

- `v81_summary_source`
- `v81_handoff_source`
- `v81_closeout_source`
- `v81_boundary_context`
- `v81_provenance_context`
- `v81_authority_gap_context`
- `v81_exception_context`
- `current_concrete_corpus_source`
- `current_customer_corpus_source`
- `current_benchmark_descriptor_source`
- `privacy_authority_source`
- `license_or_consent_authority_source`
- `customer_data_authority_source`
- `connector_authority_source`
- `endpoint_authority_source`
- `transfer_boundary_source`
- `explicit_corpus_absence_marker`
- `explicit_authority_absence_marker`
- `dogfood_context`
- `roadmap_context`
- `support_process_context`
- `absence_marker`

Minimum `source_content_horizon` values:

- `corpus_content_reference`
- `corpus_descriptor_only`
- `benchmark_descriptor_only`
- `customer_corpus_reference`
- `connector_identifier_only`
- `endpoint_identifier_only`
- `privacy_or_license_authority_source`
- `explicit_absence_marker`

Minimum `source_permission_posture` values:

- `permission_not_claimed`
- `permission_explicitly_absent`
- `permission_requires_later_authority`
- `permission_source_present_for_review_only`
- `not_applicable`

Descriptor, connector-identifier, endpoint-identifier, and absence-marker rows
may support recordability or blockers. They do not satisfy
`eligible_for_corpus_ingestion_review` by themselves.

`repo_corpus_ingestion_review_request@1` should include:

- `request_rows`
  - `corpus_ingestion_review_request_ref`
  - `candidate_ref`
  - `source_refs`
  - `v81_summary_refs`
  - `v81_handoff_refs`
  - `v81_closeout_refs`
  - `requested_corpus_ingestion_review_horizon`
  - `ingestion_review_posture`
  - `corpus_source_currentness`
  - `required_privacy_posture`
  - `required_license_posture`
  - `required_customer_data_posture`
  - `required_connector_posture`
  - `required_endpoint_posture`
  - `requested_preflight_horizon`
  - `requested_connector_boundary_horizon`
  - `requested_data_handling_authority_horizon`
  - `guardrail_refs`
  - `corpus_ingestion_posture`
  - `data_transfer_posture`
  - `customer_data_handling_posture`
  - `connector_activation_posture`
  - `endpoint_access_posture`
  - `adjudication_execution_posture`
  - `odeu_lanes`
  - `limitation_note`

Optional embedded `authority_requirement_rows` should include:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_before_surface`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum `ingestion_review_posture` values:

- `request_recorded_absence_only`
- `request_recorded_boundary_only`
- `eligible_for_corpus_ingestion_review`
- `blocked_by_missing_v81_handoff`
- `blocked_by_missing_corpus_source`
- `blocked_by_missing_privacy_authority`
- `blocked_by_missing_license_or_consent`
- `blocked_by_missing_customer_data_authority`
- `blocked_by_missing_connector_authority`
- `blocked_by_missing_endpoint_authority`
- `blocked_by_missing_transfer_boundary`
- `blocked_by_product_authority_gap`
- `blocked_by_benchmark_truth_guardrail`
- `blocked_by_graph_memory_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

`repo_corpus_ingestion_non_transfer_guardrail@1` should include:

- `guardrail_rows`
  - `guardrail_ref`
  - `candidate_ref`
  - `source_refs`
  - `forbidden_ingestion_actions`
  - `forbidden_transfer_actions`
  - `forbidden_connector_actions`
  - `forbidden_endpoint_actions`
  - `forbidden_downstream_authority`
  - `required_later_authority_refs`
  - `authority_requirement_rows`
  - `non_ingestion_posture`
  - `non_transfer_posture`
  - `non_connector_posture`
  - `limitation_note`

## Validation Requirements

`V82-A` should enforce:

- every request row references known source rows;
- every source row has concrete source posture or explicit absence posture;
- support / dogfood / roadmap context cannot be the only eligibility source;
- released `V81-C` handoff or summary refs are required for ordinary request
  recordability;
- eligible rows cite released `V81-C` substrate and a current concrete corpus
  or customer corpus source with `source_content_horizon` set to
  `corpus_content_reference` or `customer_corpus_reference`;
- rows with only explicit absence sources must use
  `request_recorded_absence_only` or a specific blocked posture, not
  `eligible_for_corpus_ingestion_review`;
- rows with only corpus descriptors, benchmark descriptors, connector
  identifiers, or endpoint identifiers must remain blocked, review-only, or
  absence-only;
- privacy, license, customer-data, connector, endpoint, and transfer boundary
  posture is source-bound or explicitly absent;
- `required_later_authority_refs` resolve to current source rows or embedded
  `authority_requirement_rows`, not future `V82-B` authority-review rows;
- customer corpus rows require privacy, license / consent, and customer-data
  authority posture;
- benchmark descriptor rows cannot claim benchmark truth;
- connector refs cannot become connector activation;
- endpoint refs cannot become endpoint access permission;
- product-pressure rows remain product-blocked or future-product-routed;
- graph-memory pressure remains graph-memory-authority-blocked or
  future-family-routed;
- future `V82-B` surfaces are represented through horizons and postures, not
  refs to non-existent rows;
- all reference rows carry no-ingestion, no-transfer, no-connector,
  no-endpoint-access, and no-adjudication-execution posture.

## Reference Fixture Intent

The first fixture should include:

- a self-evidencing workflow row recorded as corpus-ingestion review pressure
  but blocked by missing concrete corpus source, privacy, license, or
  connector authority depending on released source rows;
- a typed-adjudication product-pressure row blocked by product authority or
  future-family-only;
- `V81-C` source rows;
- dogfood and roadmap rows marked context-only;
- explicit absence rows for missing corpus source, privacy, license/customer,
  connector, endpoint, or transfer authority;
- non-transfer guardrails for each candidate;
- zero preflight, connector-boundary, data-handling-authority, exception,
  summary, handoff, ingestion, connector, endpoint, product, release,
  graph-memory, or `V83` rows.

## Mandatory Reject Fixtures

Reject fixtures should cover:

- request row with unknown source ref;
- source row without concrete source or explicit absence posture;
- eligible request with only dogfood / support / roadmap sources;
- eligible request without released `V81-C` handoff or summary refs;
- eligible request relying only on explicit absence rows;
- eligible request relying only on descriptor, connector identifier, or
  endpoint identifier rows;
- request row that treats connector identifier as activation authority;
- request row that treats endpoint identifier as access permission;
- request row that treats public URL as ingestion permission;
- customer corpus row without privacy / license / customer authority posture;
- benchmark descriptor row claiming benchmark truth;
- product-pressure row marked ingestion-ready;
- graph-memory row marked living-memory-authorized;
- request row with non-empty `V82-B` refs;
- guardrail with empty forbidden ingestion / transfer / connector / endpoint
  actions;
- row claiming corpus ingestion, connector activation, endpoint access,
  data transfer, cross-corpus adjudication execution, product authorization,
  release, graph-memory authority, recursive policy amendment, or `V83`
  selection.

## Closeout Posture

When `V82-A` closes, the slice closeout should state:

- `V82-A` created corpus-ingestion review request, source index, and
  non-transfer guardrail surfaces;
- `V82-A` did not create preflight, connector boundary, data-handling
  authority, exception, summary, or handoff surfaces;
- `V82-A` did not ingest corpora, transfer data, handle customer data,
  activate connectors, access endpoints, execute cross-corpus adjudication,
  productize, release, create graph memory authority, amend recursive policy,
  or select `V83`.
