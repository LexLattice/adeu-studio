# Draft ADEU Cross-Corpus Governance V81-B Implementation Mapping v0

Status: support / slice implementation mapping for planned `V81-B`.

Authority layer: support.

This note scopes the second `V81` slice. It is not an implementation lock.
`V81-B` should become active only after `V81-A` closes and a future canonical
starter trio selects it.

## Slice Intent

`V81-B` should extend released `V81-A` request / source / guardrail substrate
with corpus boundary contracts, imported-substrate provenance, authority gap
registers, and exception visibility. It must remain review-only: boundary
contracts do not transfer corpus data, provenance rows do not claim truth,
authority gap rows do not grant authority, and exceptions are not resolved by
prose.

It must not ingest corpora, handle customer data, activate connectors, access
external endpoints, execute cross-corpus adjudication, productize, release,
create graph memory, or select `V82`.

## Selected Surfaces

`V81-B` should select only:

- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/cross_corpus_governance.py`
- schema and mirror schema files for the four selected surfaces
- `packages/adeu_repo_description/tests/test_cross_corpus_governance_v81b.py`
- `apps/api/fixtures/repo_description/vnext_plus228/repo_corpus_boundary_contract_v228_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus228/repo_imported_substrate_provenance_register_v228_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus228/repo_cross_corpus_authority_gap_register_v228_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus228/repo_cross_corpus_exception_register_v228_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus228/repo_cross_corpus_governance_v228_reject_*.json`

## Consumed Substrate

`V81-B` should consume released `V81-A` rows:

- `repo_cross_corpus_governance_request@1`
- `repo_cross_corpus_source_index@1`
- `repo_cross_corpus_non_ingestion_guardrail@1`

It should not create a parallel cross-corpus universe. Every `V81-B` row should
reference known `V81-A` request, source, and guardrail rows.

## Minimum Row Fields

`repo_corpus_boundary_contract@1` should include:

- `boundary_contract_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `guardrail_refs`
- `corpus_horizon_kind`
- `corpus_scope_refs`
- `boundary_resolution_kind`
- `allowed_corpus_review_actions`
- `forbidden_corpus_actions`
- `privacy_clearance_posture`
- `license_or_consent_posture`
- `customer_data_handling_posture`
- `data_handling_posture`
- `corpus_transfer_posture`
- `connector_activation_posture`
- `limitation_note`

`repo_imported_substrate_provenance_register@1` should include:

- `provenance_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `boundary_contract_refs`
- `substrate_kind`
- `capture_posture`
- `provenance_status`
- `truth_status_forbidden`
- `benchmark_truth_posture`
- `limitation_note`

`repo_cross_corpus_authority_gap_register@1` should include:

- `authority_gap_ref`
- `candidate_ref`
- `request_refs`
- `source_refs`
- `boundary_contract_refs`
- `provenance_refs`
- `authority_kind`
- `authority_gap_posture`
- `required_before_surface`
- `source_presence_posture`
- `limitation_note`

`repo_cross_corpus_exception_register@1` should include:

- `exception_ref`
- `candidate_ref`
- `request_refs`
- `boundary_contract_refs`
- `provenance_refs`
- `authority_gap_refs`
- `exception_kind`
- `blocking_posture`
- `visibility_posture`
- `required_next_surface`
- `limitation_note`

## Vocabulary

Minimum boundary resolution kind:

- `concrete_repo_file_ref`
- `concrete_external_source_ref`
- `bounded_public_corpus_descriptor`
- `bounded_customer_corpus_descriptor`
- `benchmark_result_descriptor`
- `paper_design_repo_bundle_descriptor`
- `synthetic_corpus_descriptor`
- `no_corpus_boundary`

Minimum data handling posture:

- `no_data_handling_performed_by_v81`
- `data_handling_requires_later_authority`
- `data_handling_forbidden_by_this_family`

Minimum privacy clearance posture:

- `clearance_not_present`
- `clearance_requires_later_authority`
- `clearance_not_applicable`
- `clearance_explicitly_absent`

Minimum license or consent posture:

- `license_not_present`
- `license_requires_later_authority`
- `consent_requires_later_authority`
- `not_applicable`
- `explicitly_absent`

Minimum customer data handling posture:

- `no_customer_data_handling_performed_by_v81`
- `customer_data_handling_requires_later_authority`
- `customer_data_handling_forbidden_by_this_family`

Minimum corpus transfer posture:

- `no_corpus_transfer_performed_by_v81`
- `corpus_transfer_requires_later_authority`
- `corpus_transfer_forbidden_by_this_family`

Minimum provenance status:

- `source_present_unverified_truth`
- `source_absent`
- `source_stale_or_incomplete`
- `provenance_requires_later_review`
- `not_applicable`

Minimum capture posture:

- `descriptor_recorded_only`
- `source_metadata_recorded_only`
- `provenance_requires_later_review`
- `corpus_content_not_captured`
- `capture_not_applicable`

Minimum authority kind:

- `maintainer_authority`
- `privacy_authority`
- `license_or_consent_authority`
- `customer_data_authority`
- `connector_authority`
- `benchmark_result_authority`
- `product_authorization`
- `external_branch_activation`
- `release_authority`
- `recursive_policy_authority`

Minimum exception kind:

- `missing_corpus_source`
- `stale_or_historical_corpus_source`
- `missing_corpus_boundary`
- `missing_imported_provenance`
- `privacy_authority_gap`
- `license_or_consent_gap`
- `customer_data_authority_gap`
- `connector_authority_gap`
- `benchmark_truth_guardrail_gap`
- `product_authority_gap`
- `external_branch_authority_gap`
- `release_authority_gap`
- `unknown_needs_review`

## Validation Requirements

`V81-B` should enforce:

- every boundary/provenance/authority/exception row references known `V81-A`
  request, source, and guardrail rows;
- boundary contracts cannot ingest, transfer, export, mutate, or handle
  external/customer corpus data;
- customer and non-public corpus boundary rows must carry privacy,
  license/consent, and customer-data handling blockers unless explicit later
  authority sources are present;
- connector identifiers cannot become connector activation;
- external endpoint refs cannot become endpoint access;
- provenance rows cannot claim corpus truth, benchmark truth, or external
  result truth, and `capture_posture` remains descriptor/metadata-only unless
  a later family selects content capture;
- authority gap rows cannot grant authority;
- exception rows cannot mark blocking exceptions resolved by prose;
- product and external branch gaps stay blockers or future-family-routed;
- no `V81-B` row selects `V81-C`, `V82`, graph memory, product authorization,
  release, connector activation, or ingestion.

## Reference Fixture Intent

The first `V81-B` reference fixture should include:

- one boundary contract over the self-evidencing row that is boundary-only or
  blocked by missing corpus source;
- one product-pressure boundary row blocked by product authority;
- provenance rows that preserve source presence or absence without truth;
- authority gap rows for privacy/license/customer/connector/product/external
  gaps where relevant;
- exception rows that carry blockers or warnings visibly;
- no ingestion, transfer, customer data handling, connector activation,
  endpoint access, adjudication execution, product authorization, release,
  summary, handoff, graph memory, or `V82` rows.

## Mandatory Reject Fixtures

Reject fixtures should cover:

- boundary row with unknown request ref;
- boundary row transferring or ingesting corpus data;
- endpoint ref treated as endpoint access permission;
- connector ref treated as connector activation;
- provenance row claiming truth;
- benchmark result row claiming benchmark truth;
- authority gap row granting authority;
- exception row resolving a blocker by prose;
- product pressure marked cross-corpus ready without product authority;
- external branch pressure marked ready without external branch authority;
- summary or handoff rows included in `V81-B`;
- `V82` selection.
