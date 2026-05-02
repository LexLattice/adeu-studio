# Draft ADEU Corpus Ingestion Authority Review V82 Implementation Mapping v0

Status: support / implementation mapping record for planned `V82`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V82` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v72.md`
- `docs/ARCHITECTURE_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V82` should add corpus-ingestion authority review records without turning them
into:

- corpus ingestion, external data import/export, or corpus transfer;
- customer data handling;
- connector activation;
- endpoint access or mutation;
- ingestion permission or data-handling clearance;
- imported truth, benchmark truth, or external result truth;
- cross-corpus adjudication execution;
- command execution, dispatch, product authorization, release, or recursive
  policy amendment;
- living-memory authority;
- `V83` or later-family selection.

The implementation target is a typed corpus-ingestion review family that can
represent:

- source-bound corpus-ingestion review requests;
- source indexes that distinguish eligibility sources from support context;
- non-transfer guardrails;
- ingestion preflight contracts without ingestion;
- connector access review boundaries without connector activation;
- data-handling authority review without clearance claims;
- exceptions without resolving them by prose;
- review summaries and post-review handoffs without later-family completion.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded corpus-ingestion authority review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus230/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V82` still describes repo/corpus review
metadata and authority posture. If a later family becomes live connector
access, external corpus ingestion, customer data handling, endpoint access,
product UI, cross-corpus adjudication execution, release automation, or graph
query runtime, that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/corpus_ingestion_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_corpus_ingestion_review_v82a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_corpus_ingestion_review_request.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_non_transfer_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_corpus_ingestion_preflight_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_connector_access_review_boundary.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_data_handling_authority_review.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_review_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_corpus_ingestion_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_corpus_ingestion_review_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_corpus_ingestion_review_request.schema.json`
- `spec/repo_corpus_ingestion_source_index.schema.json`
- `spec/repo_corpus_ingestion_non_transfer_guardrail.schema.json`
- `spec/repo_corpus_ingestion_preflight_contract.schema.json`
- `spec/repo_connector_access_review_boundary.schema.json`
- `spec/repo_corpus_data_handling_authority_review.schema.json`
- `spec/repo_corpus_ingestion_exception_register.schema.json`
- `spec/repo_corpus_ingestion_review_summary.schema.json`
- `spec/repo_post_corpus_ingestion_review_handoff.schema.json`
- `spec/repo_corpus_ingestion_review_family_closeout_alignment.schema.json`

## 3. Candidate `V82` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_corpus_ingestion_review_request@1` | `V82-A` | request rows over released `V81-C` substrate, with recordability separated from eligibility |
| `repo_corpus_ingestion_source_index@1` | `V82-A` | concrete corpus, privacy, license, connector, endpoint, support, and absence source rows |
| `repo_corpus_ingestion_non_transfer_guardrail@1` | `V82-A` | non-ingestion, non-transfer, non-connector, non-endpoint, non-product, non-release, and non-policy guardrails |
| `repo_corpus_ingestion_preflight_contract@1` | `V82-B` | preflight posture without corpus import or data transfer |
| `repo_connector_access_review_boundary@1` | `V82-B` | connector / endpoint review boundary without activation or access |
| `repo_corpus_data_handling_authority_review@1` | `V82-B` | privacy, license, consent, retention, deletion, and customer-data authority review without clearance grants |
| `repo_corpus_ingestion_exception_register@1` | `V82-B` | missing source, missing authority, connector, endpoint, product, benchmark, graph, and unknown blockers |
| `repo_corpus_ingestion_review_summary@1` | `V82-C` | synthesis of corpus-ingestion review readiness without ingestion |
| `repo_post_corpus_ingestion_review_handoff@1` | `V82-C` | later-review handoff after corpus-ingestion review |
| `repo_corpus_ingestion_review_family_closeout_alignment@1` | `V82-C` | family closeout alignment without ingestion or connector activation |

`V82-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement preflight contracts,
connector boundaries, data-handling authority rows, exception registers,
summaries, handoffs, corpus ingestion, connector activation, product
workbenching, graph memory, or release authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V81` cross-corpus governance family closeout:
  - `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v229/evidence_inputs/v81_family_closeout_alignment_v229.json`
  - `artifacts/agent_harness/v229/evidence_inputs/v81c_cross_corpus_governance_closeout_evidence_v229.json`
- `V81-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_summary_v229_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_post_cross_corpus_review_handoff_v229_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus229/repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json`
- released `V81-B` context:
  - `apps/api/fixtures/repo_description/vnext_plus228/repo_corpus_boundary_contract_v228_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus228/repo_imported_substrate_provenance_register_v228_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus228/repo_cross_corpus_authority_gap_register_v228_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus228/repo_cross_corpus_exception_register_v228_reference.json`
- support lineage:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become corpus-ingestion source rows.

If a concrete corpus source, privacy source, license/consent source, customer
authority source, connector authority source, endpoint authority source, or
transfer boundary source is missing when an active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct ingestion eligibility from planning prose.

## 5. Shared Row Vocabulary

Minimum corpus-ingestion source row fields:

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

Minimum ingestion source role:

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

Rows with `dogfood_context`, `roadmap_context`, or `support_process_context`
may contextualize `V82-A`; they cannot be the only sources for
`eligible_for_corpus_ingestion_review`.

Minimum source content horizon:

- `corpus_content_reference`
- `corpus_descriptor_only`
- `benchmark_descriptor_only`
- `customer_corpus_reference`
- `connector_identifier_only`
- `endpoint_identifier_only`
- `privacy_or_license_authority_source`
- `explicit_absence_marker`

Minimum source permission posture:

- `permission_not_claimed`
- `permission_explicitly_absent`
- `permission_requires_later_authority`
- `permission_source_present_for_review_only`
- `not_applicable`

Rows with `corpus_descriptor_only`, `benchmark_descriptor_only`,
`connector_identifier_only`, `endpoint_identifier_only`, or
`explicit_absence_marker` do not satisfy corpus-content eligibility by
themselves. They may support request recordability, blockers, or later
authority review only.

Minimum corpus-ingestion request fields:

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

Minimum embedded authority requirement row fields for `V82-A` guardrail or
request payloads:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_before_surface`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum ingestion review posture:

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

Minimum requested ingestion horizon:

- `corpus_ingestion_authority_review`
- `connector_access_authority_review`
- `customer_data_handling_authority_review`
- `benchmark_descriptor_ingestion_review`
- `repo_local_corpus_transfer_review`
- `future_family_only`

`eligible_for_corpus_ingestion_review` requires released `V81-C` substrate, a
current concrete corpus or customer corpus source with
`source_content_horizon = corpus_content_reference` or
`customer_corpus_reference`, relevant privacy/license/customer authority
posture, and non-transfer guardrail refs. If only descriptors, connector
identifiers, endpoint identifiers, support rows, or explicit absence rows
exist, `ingestion_review_posture` must be `request_recorded_absence_only` or a
specific blocked posture.

## 6. Family Validation Themes

The family should enforce:

- support / dogfood / roadmap context cannot be the only eligibility source;
- V81-C handoff pressure is necessary but not sufficient for eligibility;
- explicit absence rows support recordability and blocker visibility, not
  readiness;
- concrete corpus source rows do not authorize ingestion or transfer;
- privacy, license, consent, customer, connector, endpoint, and transfer
  authority must be source-bound or explicitly absent;
- product pressure remains product-routed and authority-bound;
- benchmark descriptors remain non-truth;
- graph-memory pressure remains future-family-only unless a later selector
  chooses it;
- every row carries no-ingestion, no-transfer, no-connector-activation,
  no-endpoint-access, and no-adjudication-execution posture where relevant.

## 7. Starter Lock Expectation

The future `vNext+230` starter lock should select only `V82-A`: request,
source-index, non-transfer guardrail schema, validators, exports, and
reference/reject fixtures.

It should not select `V82-B`, `V82-C`, preflight contracts, connector access
boundaries, data-handling authority reviews, exception registers, summaries,
handoffs, corpus ingestion, connector activation, endpoint access,
customer-data handling, cross-corpus adjudication execution, product
authorization, release, benchmark truth, graph-memory authority, or `V83`.
