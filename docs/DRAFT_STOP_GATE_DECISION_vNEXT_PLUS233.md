# Draft Stop-Gate Decision vNext+233

Status: pre-start scaffold decision for `V83-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS233.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+233` / `V83-A` only.
- It does not claim implementation has started or passed.
- It does not redefine the lock in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS233.md`.
- It does not authorize `V83-B`, `V83-C`, edge decomposition rows, artifact
  obligation maps, drift / ambiguity registers, projection packets,
  intent-to-work-packet handoffs, implementation, code edits, command
  execution, tool invocation, worker dispatch, meta-orchestrator runtime,
  Morphic UX runtime changes, direct OAI runtime behavior, product
  authorization, PR creation, commit, merge, release, graph-memory authority,
  recursive policy amendment, or `V84` selection.

## Starter Decision

The starter bundle is acceptable for implementation drafting if it preserves
the following path:

```text
released V82-C / support doctrine / operator intent
  -> intent source rows
  -> semantic intent contract rows
  -> non-implementation guardrails
  -> later V83-B edge decomposition only after V83-A closes
```

The key starter decision is to select only the `V83-A` record shapes:

- `repo_semantic_intent_contract@1`
- `repo_intent_source_index@1`
- `repo_intent_non_implementation_guardrail@1`

## Required Pre-Start Inputs

Required planning / support documents:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v73.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_V83A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_SEMANTIC_IMPLEMENTATION_SPECIFICATION_V83_PLANNING_v0.md`

Required released substrate:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS232.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS232.md`
- `docs/ASSESSMENT_vNEXT_PLUS232_EDGES.md`
- `docs/DRAFT_ADEU_CORPUS_INGESTION_AUTHORITY_REVIEW_V82_FAMILY_CLOSEOUT_v0.md`
- released `V82-C` reference fixtures and closeout evidence inputs cited by
  the lock.

Support sources that must be source-bound, imported, or absence-marked before
lock-level fixture use:

- `docs/support/morphic_ux. v2.md`
- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/META_ORCHESTRATOR_LOOP_ODEU_SPEC.md`
- `/home/rose/work/LexLattice/codex-review-shell-direct/docs/OAI_CODEX_UPSTREAM_ODEU_PROFILE.md`

## Exit Criteria For Future Closeout

The future `vNext+233` closeout decision should be allowed to pass only if:

| Criterion | Required State |
|---|---|
| `V83-A` implementation merged | one ready-for-review PR merged to `main` |
| Package scope | `adeu_repo_description` only unless explicitly justified by the lock |
| Selected surfaces | exactly `repo_semantic_intent_contract@1`, `repo_intent_source_index@1`, `repo_intent_non_implementation_guardrail@1` |
| Recordability / eligibility | distinct fields and validators prove support-only / absence-only / generated-only rows cannot become eligible |
| Generated spec provenance | model/agent rows are candidate-only and require prompt/profile/source/generation posture |
| Intent shape | eligible contracts require non-goals, semantic and operational constraints, authority boundaries, and typed success horizon |
| Support source readiness | Morphic UX and direct-harness sources are repo-owned, imported as external support, or absence-marked |
| Guardrails | forbidden implementation, runtime, and downstream authority actions are non-empty |
| Deferred surfaces | no `V83-B` or `V83-C` rows ship in `V83-A` |
| Verification | focused `V83-A` tests plus export-schema parity pass, and `make check` passes before PR merge |
| Closeout docs/artifacts | docs/artifacts-only closeout bundle passes `make arc-closeout-check ARC=233` |

## Current Decision

- decision: `STARTER_SCAFFOLD_READY_FOR_V83A_IMPLEMENTATION_DRAFTING`
- current authority: pre-start scaffold only
- rationale:
  - the reviewed V83 planning bundle selects the correct family and slice;
  - the lock selects only the semantic intent contract / source-index /
    non-implementation guardrail starter seam;
  - recordability versus eligibility, generated-spec provenance, typed success
    horizons, source-bound non-goals, and support-source import / absence
    posture are now explicit starter obligations;
  - implementation, work-packet execution, runtime behavior, Morphic UX
    runtime changes, direct OAI runtime behavior, product, release, graph
    memory, recursive policy amendment, and `V84` remain forbidden.

The decision remains non-authoritative until the implementation and closeout
evidence are produced.
