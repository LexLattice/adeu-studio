# Draft Stop-Gate Decision vNext+240

Status: pre-start scaffold decision for `V85-B`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS240.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+240` / `V85-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS240.md`.
- It does not use `V85-B` to authorize `V85-C`, declaration summaries,
  post-declaration handoffs, obligation expansion, evidence contracts, edge
  probe plans, reviewer taskpacks, audit reports, deterministic closeout
  routing, implementation locks, work-packet activation, code edits, command
  execution, tool invocation, target mutation, runtime transition, product
  authorization, graph-memory authority, recursive policy amendment, or `V86`
  selection.

## Pre-Start Decision

- gate decision:
  - `V85B_CANONICAL_LOOKUP_REGISTRY_STARTER_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - `V85-A` is now closed on `main` as the declaration request / source-index
    / non-authority guardrail intake slice;
  - the family selector already names `V85-B` as the next default candidate;
  - the active starter slice selects only canonical lookup index, semantic
    operator/class registry, obligation-family registry, and semantic pointer
    lookup fixture records;
  - lookup rows remain review-only and do not prove natural semantic truth;
  - registry rows remain lookup semantics and do not create runtime behavior
    or authority;
  - obligation-family rows are named for later expansion only;
  - opaque pointer fixtures prove pointer obedience only;
  - obligation expansion, evidence contracts, audit, closeout routing,
    implementation, runtime behavior, product authority, graph authority,
    recursive policy amendment, and `V86` remain unselected.

## Planned Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Selected slice is only `V85-B` | required | planned |
| Implementation package is only `adeu_repo_description` | required | planned |
| Selected surfaces are the four `V85-B` records | required | planned |
| Released `V85-A` substrate is source-bound | required | planned |
| Declaration session and candidate identity stay coherent | required | planned |
| Canonical lookup status does not become semantic truth | required | planned |
| Pointer grammar fails closed on malformed / unknown inputs | required | planned |
| Duplicate and order preservation are explicit | required | planned |
| Registry aliases require alias rows | required | planned |
| Unknown versions do not become latest versions by default | required | planned |
| Operator semantics remain declaration-only | required | planned |
| Obligation families are not expanded into obligations | required | planned |
| Opaque pointer fixture success stays pointer-obedience-only | required | planned |
| Deferred `V85-C` and `V86` surfaces stay deferred | required | planned |

## Required Local Gate

- docs-only starter-bundle check:
  - `make arc-start-check ARC=240`
- implementation PR gate after code changes:
  - `make check`

## Recommendation

Proceed to the bounded `V85-B` implementation slice only after this starter
bundle passes `make arc-start-check ARC=240`.
