# Draft Stop-Gate Decision vNext+221

Status: pre-start scaffold for `V79-A`.

Authority layer: lock-readiness scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS221.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+221` / `V79-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS221.md`.
- It does not use `V79-A` to authorize `V79-B`, `V79-C`, run plans,
  tool-invocation plans, effect-monitoring contracts, exception registers,
  summaries, handoffs, command execution, tool invocation, target mutation,
  accepted effects, observed telemetry, verified rollback, worker assignment,
  dispatch execution, product authorization, external branch activation, PR
  creation, commit, merge, release, benchmark truth, global model selection,
  living-memory authority, recursive policy amendment, or `V80` selection.

## Pre-Start Decision

Proceed to a bounded `V79-A` implementation branch only if the implementation
selects exactly these starter surfaces:

- `repo_controlled_execution_review_request@1`
- `repo_controlled_execution_source_index@1`
- `repo_controlled_execution_non_execution_guardrail@1`

The first implementation branch should remain in `adeu_repo_description`, add
schema mirrors under `spec/`, and add reference / reject fixtures under
`apps/api/fixtures/repo_description/vnext_plus221/`.

## Accept When

- controlled-execution review requests resolve to concrete `V78-C` source rows
  or explicit absence rows;
- support / dogfood context cannot be the only eligibility source;
- future run-plan and tool-invocation pressure is represented with horizons
  and required postures, not refs to unshipped `V79-B` surfaces;
- every reference row carries no-controlled-execution, no-execution, and
  no-tool-invocation posture;
- product and external pressure remain blocked or future-family-routed;
- non-execution guardrails carry non-empty forbidden action and downstream
  authority lists.

## Do Not Accept When

- a request row creates or references a `V79-B` run plan, tool-invocation plan,
  monitoring contract, telemetry success row, rollback verification row, or
  operator-confirmation artifact as if it already exists;
- a `V78` authority decision is treated as execution authorization;
- a `V78` tool-use envelope is treated as tool invocation;
- a command-scope boundary is treated as target mutation authority;
- command output, local tool output, model suggestion, or operator desire is
  treated as authority evidence;
- the slice claims command execution, tool invocation, target mutation,
  accepted effects, observed telemetry, verified rollback, product
  authorization, external activation, release, or `V80` selection.

## Local Gate

For the docs-only starter bundle:

```bash
make arc-start-check ARC=221
```

Before any Python implementation PR for `V79-A`:

```bash
make check
```
