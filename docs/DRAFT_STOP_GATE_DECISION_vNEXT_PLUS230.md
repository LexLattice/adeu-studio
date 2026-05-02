# Draft Stop-Gate Decision vNext+230

Status: pre-start scaffold for `V82-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS230.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+230` / `V82-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS230.md`.
- It does not authorize `V82-B`, `V82-C`, ingestion preflight contracts,
  connector access review boundaries, data-handling authority review rows,
  exception registers, summaries, handoffs, corpus ingestion, external data
  import/export, customer-data handling, connector activation, endpoint
  access, data transfer, cross-corpus adjudication execution, product
  authorization, PR creation, commit, merge, release, benchmark truth,
  imported-result truth, graph-memory authority, recursive policy amendment,
  or `V83` selection.

## Starter Evidence Basis

Expected source rows for the active implementation should be drawn from:

- released `V81-C` starter and closeout docs:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS229.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS229.md`
  - `docs/ASSESSMENT_vNEXT_PLUS229_EDGES.md`
- released `V81` family closeout docs and artifacts:
  - `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v229/evidence_inputs/v81_family_closeout_alignment_v229.json`
  - `artifacts/agent_harness/v229/evidence_inputs/v81c_cross_corpus_governance_closeout_evidence_v229.json`
- released `V81-C` reference and reject fixtures under:
  - `apps/api/fixtures/repo_description/vnext_plus229/`
- support-level family planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v72.md`
  - `docs/ARCHITECTURE_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_FAMILY_v0.md`
  - `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82A_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82B_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82C_IMPLEMENTATION_MAPPING_v0.md`
- combined support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_COMBINED_DOGFOOD_TEST_v0.json`

Support and roadmap rows may contextualize `V82-A`, but they must not be the
only source for `eligible_for_corpus_ingestion_review`.

## Required Implementation Scope

`vNext+230` should select only:

- `repo_corpus_ingestion_review_request@1`
- `repo_corpus_ingestion_source_index@1`
- `repo_corpus_ingestion_non_transfer_guardrail@1`

Expected implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/corpus_ingestion_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- schema and mirror schema files for the three selected `V82-A` surfaces
- `packages/adeu_repo_description/tests/test_corpus_ingestion_review_v82a.py`
- deterministic reference and reject fixtures under:
  - `apps/api/fixtures/repo_description/vnext_plus230/`

## Pre-Start Exit Criteria

The starter bundle is ready to implement when:

- the lock, decision, and assessment trio exists for `vNext+230`;
- the lock targets `V82-A` only;
- `make arc-closeout-check ARC=229` passes for the `V81` closeout bundle;
- `make arc-start-check ARC=230` passes for the `V82-A` starter bundle.

The implementation PR must later run the normal Python pre-PR gate required by
repo guidance.

## Initial Decision

- gate posture:
  - `NOT_YET_STARTED`
- recommended branch:
  - `arc/v82-r1`
- implementation may begin after this docs-only starter bundle is committed on
  `main`.
