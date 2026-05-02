# Draft ADEU Cross-Corpus Governance V81-C Implementation Mapping v0

Status: support / slice implementation mapping for planned `V81-C`.

Authority layer: support.

This note scopes the final `V81` slice. It is not an implementation lock.
`V81-C` should become active only after `V81-B` closes and a future canonical
starter trio selects it.

## Slice Intent

`V81-C` should summarize released `V81-A` and `V81-B` substrate, emit
post-cross-corpus-review handoffs, and close the `V81` family without
ingesting corpora, activating connectors, handling customer data, executing
cross-corpus adjudication, productizing, releasing, creating graph memory, or
selecting `V82`.

## Selected Surfaces

`V81-C` should select only:

- `repo_cross_corpus_governance_summary@1`
- `repo_post_cross_corpus_review_handoff@1`
- `repo_cross_corpus_governance_family_closeout_alignment@1`

Expected files:

- updates to `packages/adeu_repo_description/src/adeu_repo_description/cross_corpus_governance.py`
- schema and mirror schema files for the three selected surfaces
- `packages/adeu_repo_description/tests/test_cross_corpus_governance_v81c.py`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_summary_v229_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_post_cross_corpus_review_handoff_v229_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_v229_reject_*.json`

## Consumed Substrate

`V81-C` should consume released `V81-A` and `V81-B` rows:

- `repo_cross_corpus_governance_request@1`
- `repo_cross_corpus_source_index@1`
- `repo_cross_corpus_non_ingestion_guardrail@1`
- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`

It should not create a parallel summary universe. Every summary and handoff row
should reference known released rows.

## Minimum Row Fields

`repo_cross_corpus_governance_summary@1` should include:

- `cross_corpus_summary_ref`
- `candidate_ref`
- `request_refs`
- `boundary_contract_refs`
- `provenance_refs`
- `authority_gap_refs`
- `exception_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `summary_posture`
- `ready_basis_posture`
- `corpus_ingestion_posture`
- `connector_activation_posture`
- `endpoint_access_posture`
- `adjudication_execution_posture`
- `product_authorization_posture`
- `release_authority_posture`
- `guardrail_refs`
- `limitation_note`

`repo_post_cross_corpus_review_handoff@1` should include:

- `handoff_ref`
- `candidate_ref`
- `summary_refs`
- `boundary_contract_refs`
- `provenance_refs`
- `authority_gap_refs`
- `carried_exception_refs`
- `handoff_target`
- `handoff_subject_horizon`
- `handoff_authority_horizon`
- `handoff_posture`
- `required_later_authority_refs`
- `corpus_ingestion_posture`
- `connector_activation_posture`
- `endpoint_access_posture`
- `adjudication_execution_posture`
- `guardrail_refs`
- `limitation_note`

`repo_cross_corpus_governance_family_closeout_alignment@1` should include:

- `family`
- `closed_by_arc`
- `closed_slice_ladder`
- `shipped_record_shapes`
- `consumed_source_families`
- `family_closed_on_main`
- `future_family_authority`
- `unselected_future_surfaces`
- `cross_corpus_boundary`
- `limitation_note`

## Vocabulary

Minimum summary posture:

- `cross_corpus_review_ready_with_no_blockers`
- `cross_corpus_review_ready_with_nonblocking_warnings`
- `blocked_by_missing_corpus_source`
- `blocked_by_missing_boundary`
- `blocked_by_missing_provenance`
- `blocked_by_missing_authority`
- `blocked_by_missing_privacy_authority`
- `blocked_by_missing_license_or_consent`
- `blocked_by_missing_customer_data_authority`
- `blocked_by_missing_connector_authority`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_authority_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum ready basis posture:

- `ready_no_blockers`
- `ready_with_nonblocking_warnings`
- `not_ready_blockers_remain`
- `authority_review_requested_for_blockers`
- `future_family_only`
- `rejected_out_of_scope`

Minimum handoff target:

- `future_corpus_ingestion_review`
- `future_connector_authority_review`
- `future_cross_corpus_adjudication_review`
- `future_product_review`
- `future_external_branch_review`
- `future_benchmark_review`
- `future_graph_memory_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff subject horizon:

- `corpus_boundary_review_package`
- `imported_substrate_provenance_review`
- `privacy_or_license_authority_gap`
- `connector_authority_gap`
- `benchmark_result_review`
- `product_authority_gap`
- `external_branch_authority_gap`
- `graph_memory_pressure`

Minimum handoff authority horizon:

- `corpus_ingestion_authority_review`
- `connector_authority_review`
- `cross_corpus_adjudication_review`
- `benchmark_truth_guardrail_review`
- `product_authority_review`
- `external_branch_authority_review`
- `graph_memory_review`

## Validation Requirements

`V81-C` should enforce:

- every summary references known `V81-A` request rows and known `V81-B`
  boundary/provenance/authority/exception rows;
- ready summaries cannot hide blocking exceptions;
- warning-ready summaries may carry warnings but not blockers;
- carried blockers prevent ordinary ready handoff posture unless the handoff
  target is explicit authority or blocker-settlement review;
- handoffs remain later-review requests only;
- corpus-ingestion handoffs require boundary, provenance, authority, privacy,
  license/customer-data, and guardrail refs, and must keep
  `corpus_ingestion_posture` as no-ingestion by `V81`;
- connector-authority handoffs require connector authority refs;
- cross-corpus adjudication handoffs require provenance, truth/benchmark
  guardrail, and later authority refs, and must keep
  `adjudication_execution_posture` as no-adjudication by `V81`;
- product handoffs require product authority refs;
- external branch handoffs require external branch authority refs or explicit
  absence/gap posture;
- graph-memory handoffs remain review requests and do not create living-memory
  authority;
- family closeout alignment closes `V81` only and does not select `V82`.

## Reference Fixture Intent

The first `V81-C` reference fixture should include:

- one summary row for self-evidencing workflow pressure, likely blocked or
  warning-ready depending on released boundary/provenance/authority substrate;
- one product-pressure summary row blocked by product authority;
- handoff rows that carry later corpus-ingestion, connector, product,
  external-branch, benchmark, or graph-memory pressure as review requests only;
- family closeout alignment closing `V81`;
- no corpus ingestion, connector activation, endpoint access, customer data
  handling, cross-corpus adjudication execution, product authorization,
  release, benchmark truth, graph memory authority, recursive policy
  amendment, or `V82` selection.

## Mandatory Reject Fixtures

Reject fixtures should cover:

- summary row with unknown request ref;
- summary row missing boundary/provenance refs while marked ready;
- warning-ready summary carrying blocking exception refs;
- handoff marked ready while carrying blockers without authority-review target;
- corpus-ingestion handoff missing privacy/license/authority refs;
- connector handoff missing connector authority refs;
- product handoff marked ready without product authority;
- external branch handoff marked ready without external branch authority or
  explicit gap posture;
- graph-memory handoff claiming living-memory authority;
- closeout row selecting `V82`;
- closeout row claiming corpus ingestion, connector activation, endpoint
  access, customer data handling, cross-corpus adjudication execution,
  benchmark truth, product authorization, release, or recursive policy
  amendment.

## Closeout Posture

When `V81-C` closes, the family closeout should state:

- `V81` closed cross-corpus governance review;
- `V81` typed source-bound corpus requests, corpus boundaries, imported
  provenance, authority gaps, exceptions, summaries, and handoffs;
- `V81` did not ingest corpora, handle customer data, activate connectors,
  access endpoints, execute cross-corpus adjudication, productize, release,
  create graph memory authority, amend recursive policy, or select `V82`.
