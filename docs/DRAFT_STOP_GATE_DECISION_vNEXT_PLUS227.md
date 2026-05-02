# Draft Stop-Gate Decision vNext+227

Status: pre-start scaffold for `V81-A`.

Authority layer: planning / pre-lock scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS227.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision scaffold is scoped to `vNext+227` / `V81-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS227.md`.
- It does not authorize `V81-B`, `V81-C`, corpus-boundary contracts,
  imported-substrate provenance registers, authority gap registers, exception
  registers, summaries, handoffs, corpus ingestion, customer-data handling,
  connector activation, endpoint access, cross-corpus adjudication execution,
  product authorization, PR creation, commit, merge, release, benchmark truth,
  imported-result truth, global model selection, living-memory authority,
  recursive policy amendment, or `V82` selection.

## Pre-Start Gate Intent

The pre-start decision is intentionally not passed yet. It records the
expected gate shape for the future `V81-A` implementation:

- implement only the three selected starter record shapes:
  - `repo_cross_corpus_governance_request@1`
  - `repo_cross_corpus_source_index@1`
  - `repo_cross_corpus_non_ingestion_guardrail@1`
- consume released `V80-C` substrate as concrete source rows;
- keep request recordability distinct from eligibility;
- represent explicit absence rows as absence-only requests or missing-source
  blockers, not readiness;
- preserve non-ingestion, non-connector, non-endpoint, and
  non-adjudication-execution guardrails;
- ship reference and reject fixtures proving the non-ingestion boundaries;
- run the Python pre-PR gate before opening the implementation PR.

## Expected Future Evidence

The future closeout decision should cite:

- merged implementation PR;
- implementation commit and review-hardening commits, if any;
- `make check` before PR or an explicitly stated narrower gate if no Python
  implementation changed;
- `make arc-closeout-check ARC=227` for the closeout bundle;
- deterministic closeout artifacts under `artifacts/`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS227_EDGES.md`.

## Current Recommendation

- gate decision:
  - `PRE_START_ONLY_NOT_PASSED`
- rationale:
  - the starter docs select a bounded `V81-A` cross-corpus governance request /
    source-index / non-ingestion guardrail seam;
  - no implementation has run yet;
  - no closeout evidence exists yet;
  - the future implementation must preserve the review-only boundary and keep
    corpus ingestion, customer data handling, connector activation, endpoint
    access, cross-corpus adjudication execution, product authorization,
    release, graph memory, recursive policy amendment, and later-family
    selection unselected.
