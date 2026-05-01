# Draft Stop-Gate Decision vNext+222

Status: pre-start scaffold for `V79-B`.

Authority layer: lock-readiness scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS222.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+222` / `V79-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS222.md`.
- It does not use `V79-B` to authorize `V79-C`, controlled-execution review
  summaries, post-controlled-execution-review handoffs, family closeout
  alignment, command execution, tool invocation, target mutation, accepted
  effects, observed telemetry, verified rollback, worker assignment, dispatch
  execution, product authorization, external branch activation, PR creation,
  commit, merge, release, benchmark truth, global model selection,
  living-memory authority, recursive policy amendment, or `V80` selection.

## Pre-Start Decision

Proceed to a bounded `V79-B` implementation branch only if the implementation
selects exactly these starter surfaces:

- `repo_execution_run_plan@1`
- `repo_tool_invocation_plan@1`
- `repo_execution_effect_monitoring_contract@1`
- `repo_controlled_execution_exception_register@1`

The first implementation branch should remain in `adeu_repo_description`, add
schema mirrors under `spec/`, and add reference / reject fixtures under
`apps/api/fixtures/repo_description/vnext_plus222/`.

## Accept When

- run plans, tool-invocation plans, monitoring contracts, and exception rows
  resolve to known `V79-A` request / source / guardrail substrate;
- source, authority, target, telemetry, rollback, and guardrail refs are
  concrete or explicitly blocked;
- `complete_for_review_only` remains review-only, not ready-to-run;
- run plans carry `no_run_performed_by_v79`;
- tool-invocation plans carry `no_tool_invocation_performed_by_v79`;
- effect-monitoring contracts do not claim observed effects, telemetry
  success, or rollback verification;
- operator confirmation requirements remain non-authorizing;
- product and external pressure remain blocked or future-family-only.

## Do Not Accept When

- a run plan executes a command or mutates a target;
- a tool-invocation plan invokes a tool or claims global tool permission;
- a glob is used as a concrete run target boundary;
- an effect-monitoring contract claims observed effect without prior
  authorized source evidence;
- a telemetry requirement becomes telemetry success;
- a rollback requirement becomes rollback verification;
- operator confirmation becomes operator authorization;
- blocking exceptions are resolved by prose;
- product or external pressure is converted into execution readiness;
- local command output is treated as authority;
- the slice emits `V79-C` summary, handoff, or closeout surfaces.

## Local Gate

For the docs-only starter bundle:

```bash
make arc-start-check ARC=222
```

Before any Python implementation PR for `V79-B`:

```bash
make check
```
