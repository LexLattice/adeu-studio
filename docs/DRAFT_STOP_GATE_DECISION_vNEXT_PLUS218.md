# Draft Stop-Gate Decision vNext+218

Status: proposed gate for `V78-A`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS218.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+218` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md`.
- It must not use `V78-A` to authorize `V78-B`, `V78-C`, runtime execution
  authority decisions, tool-use permission envelopes, command-scope
  authorization boundaries, exception registers, readiness summaries,
  pre-execution-authority-review handoffs, command execution, tool invocation,
  worker assignment, dispatch execution, product authorization, external
  branch activation, PR creation, commit, merge, release, benchmark truth,
  global model selection, living-memory authority, or recursive policy
  amendment.

## Accept When

- `repo_runtime_execution_authority_request@1`,
  `repo_runtime_authority_source_index@1`, and
  `repo_runtime_authority_non_action_guardrail@1` schemas validate and export
  cleanly;
- implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V77-C` authority / summary / handoff /
  closeout material as concrete source rows;
- support / dogfood rows are context only and cannot be the only eligibility
  sources for runtime authority readiness;
- required authority is represented through typed authority requirement rows;
- product-pressure rows remain product-blocked or future-product-review-routed;
- external-branch rows remain external-blocked or future-family-only unless
  concrete `V43` posture exists;
- command preflight is not treated as command execution or command-scope
  authorization;
- reference rows carry `execution_posture = no_execution_performed_by_v78`;
- reference rows carry `tool_invocation_posture =
  no_tool_invocation_performed_by_v78`;
- non-action guardrails have non-empty forbidden runtime and downstream
  authority lists;
- focused tests for the new `V78-A` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- runtime authority requests reference unknown `V77-C` rows;
- runtime authority requests omit source refs;
- missing sources are represented without explicit absence posture;
- support / dogfood sources are the only eligibility sources;
- required authority is represented as untyped free text;
- product pressure is converted into runtime-authority-ready posture;
- external branch pressure is converted into runtime-authority-ready posture
  without concrete `V43` posture;
- command preflight plus target refs are treated as command-scope
  authorization;
- command preflight is treated as command execution;
- local command output or a passing tool result is treated as authority
  evidence;
- tool-use request is converted into tool invocation;
- guardrail rows have empty forbidden runtime actions or downstream authority;
- `V78-A` emits authority decision, tool-use permission envelope,
  command-scope authorization boundary, exception register, readiness summary,
  handoff, closeout, command execution, tool invocation, product
  authorization, external activation, release, or recursive policy amendment
  rows.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=218`
- before any Python implementation PR:
  - `make check`
