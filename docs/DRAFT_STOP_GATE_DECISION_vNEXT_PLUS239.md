# Draft Stop-Gate Decision vNext+239

Status: pre-start scaffold decision for `V85-A`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS239.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+239` / `V85-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md`.
- It does not use `V85-A` to authorize `V85-B`, `V85-C`, canonical lookup
  indexes, registries, pointer fixtures, summaries, handoffs, obligation
  expansion, evidence contracts, edge probe plans, audit taskpacks,
  deterministic closeout routing, implementation locks, work-packet
  activation, code edits, command execution, tool invocation, target mutation,
  runtime transition, product authorization, graph-memory authority,
  recursive policy amendment, or `V86` selection.

## Pre-Start Decision

- gate decision:
  - `V85A_SEMANTIC_DECLARATION_REQUEST_STARTER_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - the family selector selects `V85` as semantic declaration and canonical
    meta-list review after closed `V84`;
  - the active starter slice selects only semantic declaration request, source
    index, and non-authority guardrail records;
  - the starter lock keeps declaration candidates separate from canonical
    lookup results and selected declarations;
  - `semantic_declaration_session_ref`, source witness rows, negative cue
    rows, and resident-model competency rows are required starter concepts;
  - ambiguity, abstain, registry gaps, malformed input, support-only sources,
    generated candidates, and opaque pointer competency remain fail-closed or
    review-only;
  - obligation expansion, evidence contracts, audit, closeout routing,
    implementation, runtime behavior, product authority, graph authority,
    recursive policy amendment, and `V86` remain unselected.

## Planned Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Selected slice is only `V85-A` | required | planned |
| Implementation package is only `adeu_repo_description` | required | planned |
| Selected surfaces are the three `V85-A` records | required | planned |
| Released `V84-C` substrate is source-bound | required | planned |
| Declaration session identity is stable | required | planned |
| Recordability remains distinct from eligibility | required | planned |
| Declaration candidates do not become selected declarations in `V85-A` | required | planned |
| Source witnesses are row-shaped and currentness-aware | required | planned |
| Negative cues route implementation / runtime / product / later-family pressure to guardrails | required | planned |
| Resident-model competencies are independent row requirements | required | planned |
| Ambiguity, abstain, registry gaps, and malformed input fail closed | required | planned |
| Opaque pointer success cannot prove natural semantic truth | required | planned |
| Deferred `V85-B/C` surfaces stay deferred | required | planned |
| `V86` is not selected | required | planned |

## Required Local Gate

- docs-only starter-bundle check:
  - `make arc-start-check ARC=239`
- implementation PR gate after code changes:
  - `make check`

## Recommendation

Proceed to the bounded `V85-A` implementation slice only after this starter
bundle passes `make arc-start-check ARC=239`.
