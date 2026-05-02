# Draft ADEU Cross-Corpus Governance V81 Implementation Mapping v0

Status: support / implementation mapping record for planned `V81`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V81` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is accepted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v71.md`
- `docs/ARCHITECTURE_ADEU_CROSS_CORPUS_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81C_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.md`

## 1. Family Intent

`V81` should add cross-corpus governance review records without turning them
into:

- external data ingestion;
- customer substrate handling;
- connector activation;
- endpoint access or mutation;
- corpus import execution;
- corpus truth, benchmark truth, or imported-result truth;
- cross-corpus adjudication execution;
- command execution, dispatch, product authorization, release, or recursive
  policy amendment;
- `V82` or later-family selection.

The implementation target is a typed cross-corpus governance review family
that can represent:

- source-bound cross-corpus governance requests;
- source indexes that distinguish eligibility sources from support context;
- non-ingestion guardrails;
- corpus boundary contracts without corpus transfer;
- imported-substrate provenance without imported truth;
- authority and privacy/license gap registers without clearance claims;
- exceptions without resolving them by prose;
- review summaries and post-review handoffs without later-family completion.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded cross-corpus governance review records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus227/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative. `V81` still describes repo/corpus review
metadata and authority posture. If a later family becomes live connector
access, external corpus ingestion, customer data handling, product UI, release
automation, or graph query runtime, that work should split.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/cross_corpus_governance.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_cross_corpus_governance_v81a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_cross_corpus_governance_request.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_non_ingestion_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_corpus_boundary_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_imported_substrate_provenance_register.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_authority_gap_register.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_exception_register.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_governance_summary.v1.json`
- `packages/adeu_repo_description/schema/repo_post_cross_corpus_review_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_cross_corpus_governance_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_cross_corpus_governance_request.schema.json`
- `spec/repo_cross_corpus_source_index.schema.json`
- `spec/repo_cross_corpus_non_ingestion_guardrail.schema.json`
- `spec/repo_corpus_boundary_contract.schema.json`
- `spec/repo_imported_substrate_provenance_register.schema.json`
- `spec/repo_cross_corpus_authority_gap_register.schema.json`
- `spec/repo_cross_corpus_exception_register.schema.json`
- `spec/repo_cross_corpus_governance_summary.schema.json`
- `spec/repo_post_cross_corpus_review_handoff.schema.json`
- `spec/repo_cross_corpus_governance_family_closeout_alignment.schema.json`

## 3. Candidate `V81` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_cross_corpus_governance_request@1` | `V81-A` | request rows over released `V80-C` substrate and concrete corpus source or absence rows, with recordability separated from eligibility |
| `repo_cross_corpus_source_index@1` | `V81-A` | concrete source rows, absence posture, and source-role classification |
| `repo_cross_corpus_non_ingestion_guardrail@1` | `V81-A` | non-ingestion, non-connector, non-product, non-release, and non-policy guardrails |
| `repo_corpus_boundary_contract@1` | `V81-B` | corpus boundary posture without corpus transfer or handling |
| `repo_imported_substrate_provenance_register@1` | `V81-B` | imported-source provenance without imported truth |
| `repo_cross_corpus_authority_gap_register@1` | `V81-B` | privacy, license, consent, maintainer, product, runtime, release, and external authority gaps |
| `repo_cross_corpus_exception_register@1` | `V81-B` | missing source, missing boundary, provenance, authority, privacy, license, connector, product, runtime, and release blockers |
| `repo_cross_corpus_governance_summary@1` | `V81-C` | synthesis of cross-corpus governance readiness without ingestion |
| `repo_post_cross_corpus_review_handoff@1` | `V81-C` | later-review handoff after cross-corpus governance review |
| `repo_cross_corpus_governance_family_closeout_alignment@1` | `V81-C` | family closeout alignment without ingestion or adjudication execution |

`V81-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement corpus-boundary contracts,
provenance registers, authority gap registers, exception registers, summaries,
handoffs, corpus ingestion, connector activation, product workbenching, graph
memory, or release authority.

## 4. Source Classes

The family should consume concrete source refs from:

- `V80` external branch activation review family closeout:
  - `docs/DRAFT_ADEU_EXTERNAL_BRANCH_ACTIVATION_REVIEW_V80_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v226/evidence_inputs/v80_family_closeout_alignment_v226.json`
  - `artifacts/agent_harness/v226/evidence_inputs/v80c_external_branch_review_closeout_evidence_v226.json`
- `V80-C` reference fixtures:
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_readiness_summary_v226_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_post_external_branch_review_handoff_v226_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus226/repo_external_branch_review_family_closeout_alignment_v226_reference.json`
- support lineage:
  - `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become cross-corpus source rows.

If a concrete imported-corpus, benchmark-result, paper/design/repo bundle,
customer corpus, or authority source is missing when an active starter lock is
drafted, the absence should be represented as an explicit source row. The
reference fixture should not reconstruct corpus eligibility from planning
prose.

## 5. Shared Row Vocabulary

Minimum cross-corpus source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `cross_corpus_source_role`
- `source_horizon`
- `limitation_note`

Minimum cross-corpus source role:

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

Rows with `dogfood_context`, `roadmap_context`, or `support_process_context`
may contextualize `V81-A`; they cannot be the only sources for
`eligible_for_cross_corpus_governance_review`.

Rows with `concrete_customer_corpus_source` require explicit privacy,
license/consent, and customer-data authority posture. They must not by
themselves authorize customer data handling.

Minimum cross-corpus governance request fields:

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

Minimum corpus horizon kind:

- `repo_local_corpus`
- `external_public_corpus`
- `customer_provided_corpus`
- `benchmark_result_corpus`
- `paper_design_repo_bundle`
- `synthetic_or_generated_corpus`
- `unknown_or_absent_corpus`
- `future_family_only`

Minimum corpus review posture:

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

Minimum corpus source currentness:

- `current_concrete_source`
- `explicit_absence_marker`
- `historical_context_only`
- `stale_or_superseded`
- `unknown_needs_review`

`eligible_for_cross_corpus_governance_review` requires released `V80-C`
substrate, a concrete corpus source role, and
`corpus_source_currentness = current_concrete_source`. If only explicit
absence rows exist, `corpus_review_posture` must be
`request_recorded_absence_only` or `blocked_by_missing_corpus_source`.

Minimum corpus ingestion posture:

- `no_corpus_ingestion_performed_by_v81`
- `corpus_ingestion_requires_later_family`
- `corpus_ingestion_forbidden_by_this_family`

Minimum connector activation posture:

- `no_connector_activation_performed_by_v81`
- `connector_activation_requires_later_family`
- `connector_activation_forbidden_by_this_family`

Minimum external endpoint access posture:

- `no_endpoint_access_performed_by_v81`
- `endpoint_access_requires_later_authority`
- `endpoint_access_forbidden_by_this_family`
- `endpoint_absent_or_unknown`

Minimum adjudication execution posture:

- `no_cross_corpus_adjudication_performed_by_v81`
- `adjudication_requires_later_family`
- `adjudication_forbidden_by_this_family`

## 6. Validation Themes

Cross-surface validators should enforce:

- eligible requests cite released `V80-C` substrate and concrete current
  corpus source rows, not only explicit absence rows;
- absence rows support request recordability and missing-source blockers, not
  readiness;
- support and roadmap sources cannot be the only eligibility source;
- customer corpus rows require explicit privacy/license/authority posture;
- benchmark result rows cannot become benchmark truth;
- external endpoint refs cannot become access permission;
- connector refs cannot become connector activation;
- corpus boundary contracts cannot become data transfer or ingestion;
- provenance registers cannot become truth;
- product pressure remains product-authority-blocked or future-product-routed;
- external branch pressure remains external-authority-blocked or future-family
  routed;
- every `V81` row carries no-ingestion and no-connector posture unless a later
  lock selects otherwise;
- closeout rows do not select `V82`.

## 7. Reference Fixture Strategy

The first `V81-A` reference fixture should include:

- one self-evidencing workflow row recorded as boundary-only or absence-only
  cross-corpus governance pressure, depending on whether a concrete current
  corpus source exists;
- one typed-adjudication product-pressure row blocked by product authority or
  future-product review;
- source rows for `V80-C` summary / handoff / closeout fixtures;
- context-only dogfood and roadmap source rows;
- explicit corpus-source absence rows if no concrete imported corpus exists;
- non-ingestion guardrails with non-empty forbidden data / connector /
  product / release / policy actions;
- zero corpus-boundary contracts, provenance registers, authority gap
  registers, exception registers, summaries, handoffs, corpus ingestion,
  connector activation, endpoint access, product authorization, release, graph
  memory, or `V82` selection rows.

## 8. Mandatory Reject Fixtures

The active `V81-A` starter should reject at least:

- request row without source refs;
- source row without concrete source or explicit absence posture;
- support-only or roadmap-only eligibility;
- customer corpus row without privacy/license/authority posture;
- benchmark result source marked benchmark truth;
- endpoint ref treated as access permission;
- connector ref treated as connector activation;
- external branch handoff treated as external activation or corpus ingestion;
- product pressure marked cross-corpus ready without product authority gap;
- future `V81-B` refs embedded in `V81-A` starter rows;
- empty non-ingestion guardrails;
- row claiming corpus ingestion, customer data handling, connector activation,
  endpoint access, cross-corpus adjudication execution, product
  authorization, release, living-memory authority, recursive policy amendment,
  or `V82` selection.

## 9. Closeout Expectation

When `V81-C` eventually closes, the family closeout should say:

- `V81` closed cross-corpus governance review;
- corpus sources, boundaries, provenance, authority gaps, exceptions,
  summaries, and handoffs are typed and source-bound;
- no corpus was ingested;
- no connector was activated;
- no endpoint was accessed;
- no customer substrate was handled;
- no benchmark truth or imported truth was claimed;
- no product authorization, release authority, graph memory, recursive policy
  amendment, or `V82` selection happened.
