# Draft ADEU Corpus Ingestion Authority Review V82-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V82-B`.

Authority layer: support.

This note scopes the second `V82` slice. It is not an implementation lock.
`V82-B` should become active only after `V82-A` closes and a future canonical
starter trio selects it.

## Slice Intent

`V82-B` should extend released `V82-A` request / source / guardrail rows with
review-only preflight, connector boundary, data-handling authority, and
exception posture. It should not perform ingestion, transfer data, handle
customer data, activate connectors, access endpoints, execute cross-corpus
adjudication, productize, release, create graph memory, or select `V83`.

## Selected Surfaces

`V82-B` should select only:

- `repo_corpus_ingestion_preflight_contract@1`
- `repo_connector_access_review_boundary@1`
- `repo_corpus_data_handling_authority_review@1`
- `repo_corpus_ingestion_exception_register@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/corpus_ingestion_review.py`
- schema and mirror schema files for the four selected surfaces
- `packages/adeu_repo_description/tests/test_corpus_ingestion_review_v82b.py`
- `apps/api/fixtures/repo_description/vnext_plus231/repo_corpus_ingestion_preflight_contract_v231_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus231/repo_connector_access_review_boundary_v231_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus231/repo_corpus_data_handling_authority_review_v231_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus231/repo_corpus_ingestion_exception_register_v231_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus231/repo_corpus_ingestion_v231_reject_*.json`

## Consumed Substrate

`V82-B` should consume released `V82-A` rows:

- `repo_corpus_ingestion_review_request@1`
- `repo_corpus_ingestion_source_index@1`
- `repo_corpus_ingestion_non_transfer_guardrail@1`

It should not create a parallel ingestion universe. Every preflight,
connector, authority, and exception row should reference known released
request, source, and guardrail rows.

## Minimum Row Fields

`repo_corpus_ingestion_preflight_contract@1` should include:

- `preflight_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `upstream_corpus_boundary_refs`
- `upstream_provenance_refs`
- `authority_review_refs`
- `connector_boundary_refs`
- `monitoring_requirement_refs`
- `rollback_requirement_refs`
- `monitoring_requirement_posture`
- `rollback_requirement_posture`
- `preflight_posture`
- `preflight_observation_posture`
- `plan_completeness_posture`
- `corpus_ingestion_posture`
- `data_transfer_posture`
- `connector_activation_posture`
- `endpoint_access_posture`
- `adjudication_execution_posture`
- `guardrail_refs`
- `limitation_note`

`repo_connector_access_review_boundary@1` should include:

- `connector_boundary_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `connector_identifier_refs`
- `endpoint_identifier_refs`
- `endpoint_ref_posture`
- `allowed_connector_review_actions`
- `forbidden_connector_actions`
- `forbidden_endpoint_actions`
- `connector_authority_posture`
- `endpoint_authority_posture`
- `connector_activation_posture`
- `endpoint_access_posture`
- `guardrail_refs`
- `limitation_note`

`repo_corpus_data_handling_authority_review@1` should include:

- `authority_review_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `authority_kind`
- `authority_review_posture`
- `required_before_surface`
- `privacy_clearance_posture`
- `license_or_consent_posture`
- `customer_data_handling_posture`
- `retention_posture`
- `deletion_or_withdrawal_posture`
- `transfer_authority_posture`
- `clearance_not_claimed_posture`
- `guardrail_refs`
- `limitation_note`

`repo_corpus_ingestion_exception_register@1` should include:

- `exception_ref`
- `candidate_ref`
- `request_refs`
- `preflight_refs`
- `connector_boundary_refs`
- `authority_review_refs`
- `exception_kind`
- `blocking_posture`
- `visibility_posture`
- `required_next_surface`
- `limitation_note`

## Vocabulary

Minimum preflight posture:

- `preflight_recorded_for_review_only`
- `preflight_blocked_by_missing_source`
- `preflight_blocked_by_missing_authority`
- `preflight_blocked_by_missing_connector_boundary`
- `preflight_blocked_by_missing_monitoring`
- `preflight_blocked_by_missing_rollback`
- `future_family_only`
- `rejected_out_of_scope`

Minimum plan completeness posture:

- `incomplete_for_review`
- `complete_for_review_only`
- `blocked_by_missing_source`
- `blocked_by_missing_authority`
- `blocked_by_missing_boundary`
- `blocked_by_missing_connector`
- `blocked_by_missing_monitoring`
- `blocked_by_missing_rollback`
- `future_family_only`

Minimum monitoring requirement posture:

- `requirement_recorded_for_review_only`
- `missing_required_monitoring`
- `monitoring_requires_later_authority`
- `not_applicable`

Minimum rollback requirement posture:

- `requirement_recorded_for_review_only`
- `missing_required_rollback`
- `rollback_requires_later_authority`
- `not_applicable`

Minimum preflight observation posture:

- `requirements_recorded_only`
- `prior_authorized_preflight_observed`
- `preflight_not_observed`
- `preflight_observation_requires_later_authority`

Minimum endpoint ref posture:

- `endpoint_identifier_only`
- `endpoint_access_requires_later_authority`
- `endpoint_access_forbidden_by_this_family`
- `endpoint_absent_or_unknown`

Minimum authority kind:

- `privacy_authority`
- `license_authority`
- `consent_authority`
- `customer_data_authority`
- `connector_authority`
- `endpoint_access_authority`
- `transfer_authority`
- `retention_authority`
- `deletion_or_withdrawal_authority`
- `product_authority`
- `benchmark_truth_guardrail_authority`
- `graph_memory_authority`

Minimum authority review posture:

- `authority_required_later`
- `authority_missing`
- `authority_present_for_review_only`
- `authority_not_applicable`
- `authority_future_family_only`
- `authority_rejected_out_of_scope`

Minimum exception kind:

- `missing_corpus_source`
- `missing_privacy_authority`
- `missing_license_or_consent`
- `missing_customer_data_authority`
- `missing_connector_authority`
- `missing_endpoint_authority`
- `missing_endpoint_access_boundary`
- `missing_transfer_boundary`
- `missing_monitoring_requirement`
- `missing_rollback_requirement`
- `missing_retention_authority`
- `missing_deletion_or_withdrawal_authority`
- `missing_data_handling_clearance`
- `stale_or_historical_corpus_source`
- `benchmark_truth_guardrail_gap`
- `product_authority_gap`
- `graph_memory_authority_gap`
- `unsupported_ingestion_horizon`
- `unknown_needs_review`

## Validation Requirements

`V82-B` should enforce:

- every row references known released `V82-A` request, source, and guardrail
  rows;
- preflight contracts do not ingest or transfer corpus data;
- preflight observation posture records requirements or prior authorized
  evidence only; it does not make preflight pass or ingestion permission
  implicit;
- `complete_for_review_only` does not imply ready to ingest;
- connector access boundaries do not activate connectors;
- endpoint refs remain identifiers and cannot authorize access;
- data-handling authority review rows do not grant clearance;
- customer-data rows require privacy, license / consent, and customer-data
  authority posture;
- monitoring requirements are not observed monitoring;
- rollback requirements are not rollback verification;
- benchmark descriptors cannot claim benchmark truth;
- product pressure remains product authority blocked or future-product-routed;
- graph-memory pressure remains future-family-only unless a later selector
  chooses it;
- exceptions may be blocking, warning, carried, or not applicable, but cannot
  be marked resolved by `V82-B`;
- every row carries no-ingestion, no-transfer, no-connector-activation,
  no-endpoint-access, and no-adjudication-execution posture where relevant.

## Reference Fixture Intent

The first `V82-B` reference fixture should include:

- a self-evidencing workflow preflight row blocked by missing corpus source,
  privacy / license, connector, or transfer boundary as appropriate;
- connector and endpoint boundary rows that are identifier-only and
  non-activating;
- data-handling authority review rows with missing or later-required privacy,
  license, customer-data, connector, and transfer authority;
- exception rows preserving missing-source and authority blockers;
- a product-pressure row that remains product-authority blocked;
- zero ingestion, transfer, customer data handling, connector activation,
  endpoint access, adjudication execution, product authorization, release,
  graph-memory authority, or `V83` rows.

## Mandatory Reject Fixtures

Reject fixtures should cover:

- preflight row with unknown request ref;
- preflight marked complete while missing required authority refs;
- preflight row claiming corpus ingestion or data transfer;
- preflight row treating requirements recorded as a preflight pass or
  ingestion permission;
- connector boundary row activating connector;
- endpoint ref treated as endpoint access permission;
- authority review row granting data-handling clearance;
- customer-data authority row without privacy / license posture;
- monitoring requirement treated as observed monitoring;
- rollback requirement treated as rollback verification;
- exception row marked resolved by `V82-B`;
- product pressure marked ingestion-ready;
- graph-memory pressure marked authorized;
- benchmark descriptor marked benchmark truth;
- row claiming connector activation, endpoint access, corpus ingestion,
  customer data handling, cross-corpus adjudication execution, release,
  recursive policy amendment, or `V83` selection.

## Closeout Posture

When `V82-B` closes, the slice closeout should state:

- `V82-B` added review-only preflight, connector boundary, data-handling
  authority, and exception rows;
- `V82-B` did not summarize or hand off the family;
- `V82-B` did not ingest corpora, transfer data, handle customer data,
  activate connectors, access endpoints, execute cross-corpus adjudication,
  productize, release, create graph memory authority, amend recursive policy,
  or select `V83`.
