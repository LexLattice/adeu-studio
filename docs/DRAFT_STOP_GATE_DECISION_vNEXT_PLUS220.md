# Draft Stop-Gate Decision vNext+220

Status: proposed gate for `V78-C`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS220.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+220` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS220.md`.
- It must not use `V78-C` to authorize command execution, tool invocation,
  worker assignment, dispatch execution, product authorization, external branch
  activation, PR creation, commit, merge, release, benchmark truth, global
  model selection, living-memory authority, recursive policy amendment, or
  selection of `V79` / any later family.

## Accept When

- `repo_runtime_authority_readiness_summary@1`,
  `repo_pre_execution_authority_review_handoff@1`, and
  `repo_runtime_execution_authority_family_closeout_alignment@1` schemas
  validate and export cleanly;
- implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V78-A` and `V78-B` material as concrete
  source rows;
- summary rows reference known `V78-A` request refs;
- ready summary rows reference known `V78-B` decision, permission, command
  scope, and exception rows;
- ready posture cannot erase blocking exception refs;
- runtime execution handoffs require command-scope refs and preserve
  later-review-only posture;
- tool invocation handoffs require bounded tool-permission refs and preserve
  no-tool-invocation posture;
- product handoffs require product authority refs and cannot become runtime
  execution handoffs;
- external handoffs require external authority refs or concrete `V43` branch
  posture;
- every handoff row carries no-execution, no-tool-invocation, and later-review
  required status;
- family closeout alignment records `V78-A`, `V78-B`, and `V78-C` as the
  closed slice ladder without selecting `V79`;
- focused tests for the new `V78-C` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- summary rows reference unknown `V78-A` requests;
- ready summary rows lack required `V78-B` decision / permission / scope refs;
- blocking exceptions are omitted from ready posture;
- handoff rows perform or schedule command execution or tool invocation;
- runtime execution handoff lacks command-scope refs;
- tool invocation handoff lacks bounded tool-permission refs;
- product or external branch pressure becomes runtime execution readiness;
- family closeout alignment claims command execution, tool invocation,
  runtime dispatch, product authorization, external branch activation, PR /
  commit / merge / release, benchmark truth, model selection,
  living-memory authority, recursive policy amendment, or `V79` selection;
- `V78-C` emits rows outside readiness summary, pre-execution-authority-review
  handoff, and family closeout alignment.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=220`
- before any Python implementation PR:
  - `make check`
