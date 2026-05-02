# Draft Stop-Gate Decision vNext+228

Status: pre-start scaffold for `V81-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS228.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+228` / `V81-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS228.md`.
- It does not authorize `V81-C`, cross-corpus governance summaries,
  post-cross-corpus-review handoffs, family closeout alignment, corpus
  ingestion, external data import/export, customer data handling, connector
  activation, endpoint access, cross-corpus adjudication execution, product
  authorization, PR creation, commit, merge, release, benchmark truth,
  imported-result truth, model selection, living-memory authority, recursive
  policy amendment, or `V82` selection.

## Starter Evidence Basis

Expected source rows for the active implementation should be drawn from:

- released `V81-A` starter and closeout docs:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS227.md`
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS227.md`
  - `docs/ASSESSMENT_vNEXT_PLUS227_EDGES.md`
- released `V81-A` closeout artifacts:
  - `artifacts/agent_harness/v227/evidence_inputs/v81a_cross_corpus_governance_closeout_evidence_v227.json`
  - `artifacts/agent_harness/v227/evidence_inputs/metric_key_continuity_assertion_v227.json`
  - `artifacts/agent_harness/v227/evidence_inputs/runtime_observability_comparison_v227.json`
- released `V81-A` reference and reject fixtures under:
  - `apps/api/fixtures/repo_description/vnext_plus227/`
- support-level family planning:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v71.md`
  - `docs/ARCHITECTURE_ADEU_CROSS_CORPUS_GOVERNANCE_FAMILY_v0.md`
  - `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_CROSS_CORPUS_GOVERNANCE_V81B_IMPLEMENTATION_MAPPING_v0.md`

Support and roadmap rows may contextualize `V81-B`, but they must not be the
only source for boundary, provenance, authority-gap, or exception eligibility.

## Required Implementation Scope

`vNext+228` should select only:

- `repo_corpus_boundary_contract@1`
- `repo_imported_substrate_provenance_register@1`
- `repo_cross_corpus_authority_gap_register@1`
- `repo_cross_corpus_exception_register@1`

Expected implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/cross_corpus_governance.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- schema and mirror schema files for the four selected `V81-B` surfaces
- `packages/adeu_repo_description/tests/test_cross_corpus_governance_v81b.py`
- deterministic reference and reject fixtures under:
  - `apps/api/fixtures/repo_description/vnext_plus228/`

## Pre-Start Exit Criteria

The starter bundle is ready to implement when:

- the lock, decision, and assessment trio exists for `vNext+228`;
- the lock targets `V81-B` only;
- `make arc-closeout-check ARC=227` passes for the `V81-A` closeout bundle;
- `make arc-start-check ARC=228` passes for the `V81-B` starter bundle.

The implementation PR must later run the normal Python pre-PR gate required
by repo guidance.

## Initial Decision

- gate posture:
  - `NOT_YET_STARTED`
- recommended branch:
  - `arc/v81-r2`
- implementation may begin after this docs-only starter bundle is committed on
  `main`.
