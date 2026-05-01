# Draft Stop-Gate Decision vNext+219

Status: proposed gate for `V78-B`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS219.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+219` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS219.md`.
- It must not use `V78-B` to authorize `V78-C`, readiness summaries,
  pre-execution-authority-review handoffs, family closeout alignment, command
  execution, tool invocation, worker assignment, dispatch execution, product
  authorization, external branch activation, PR creation, commit, merge,
  release, benchmark truth, global model selection, living-memory authority,
  recursive policy amendment, or selection of a later family.

## Accept When

- `repo_runtime_execution_authority_decision@1`,
  `repo_tool_use_permission_envelope@1`,
  `repo_command_scope_authorization_boundary@1`, and
  `repo_runtime_authority_exception_register@1` schemas validate and export
  cleanly;
- implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V78-A` request / source / guardrail
  material as concrete source rows;
- authority decisions reference known `V78-A` requests and non-action
  guardrails;
- grant-like decision posture cites concrete authority sources and an explicit
  later-review-only horizon;
- reference rows carry `execution_authorization_posture =
  execution_not_authorized_by_v78`;
- reference rows carry `execution_posture = no_execution_performed_by_v78`;
- tool-use permission envelopes are target-bound and horizon-bound;
- global tool permission is rejected;
- tool applicability is not treated as tool-use permission;
- command-scope boundaries cite concrete targets and reject globs as concrete
  authorization boundaries;
- target scope is not treated as permission to mutate targets inside `V78`;
- product and external pressure remains blocked or future-family-routed unless
  matching authority exists;
- local command output and passing tool results cannot become authority
  evidence;
- exception rows cannot be resolved by prose only;
- focused tests for the new `V78-B` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- decision rows reference unknown `V78-A` requests or guardrails;
- grant-like decision posture lacks concrete authority source refs;
- authority grant language omits an explicit later-review-only horizon;
- authority decisions imply command execution or tool invocation;
- tool-use envelopes grant global tool permission;
- tool-use permission is inferred from earlier tool applicability;
- command-scope boundaries use globs as concrete target boundaries;
- target refs are treated as permission to mutate targets;
- product or external branch pressure is granted as runtime execution
  authority;
- local command output or passing tool results are treated as authority
  evidence;
- exception rows are marked resolved by prose only;
- `V78-B` emits readiness summaries, pre-execution-authority-review handoffs,
  family closeout alignment, command execution, tool invocation, worker
  assignment, dispatch execution, product authorization, external activation,
  PR / commit / merge / release, benchmark truth, model selection,
  living-memory authority, or recursive policy amendment rows.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=219`
- before any Python implementation PR:
  - `make check`
