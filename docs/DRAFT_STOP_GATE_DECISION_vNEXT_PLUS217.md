# Draft Stop-Gate Decision vNext+217

Status: proposed gate for `V77-C`.

Authority layer: starter-bundle scaffold, not closeout evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS217.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+217` only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS217.md`.
- It must not use `V77-C` to authorize `V78`, command execution, runtime
  permission grants, tool-use permission, worker assignment, dispatch
  execution, product authorization, external branch activation, PR creation,
  commit, merge, release, benchmark truth, global model selection,
  living-memory authority, or recursive policy amendment.

## Accept When

- `repo_runtime_permission_authority_posture@1`,
  `repo_runtime_permission_review_summary@1`,
  `repo_post_runtime_permission_review_handoff@1`, and
  `repo_runtime_permission_family_closeout_alignment@1` schemas validate and
  export cleanly;
- implementation stays in the repo-description lane unless a later lock
  explicitly selects a different package;
- reference fixtures consume released `V77-A` request / source / guardrail
  material and released `V77-B` preflight / effect / telemetry / rollback
  material as concrete source rows;
- authority posture rows record required or missing authority only;
- authority posture rows cannot grant runtime permission or tool-use
  permission;
- summary rows preserve blocking source, authority, telemetry, rollback, and
  target-boundary gaps;
- ready posture is not emitted while blocking gaps remain;
- post-runtime-permission-review handoff rows remain later-review requests and
  carry `runtime_permission_execution_posture =
  no_runtime_permission_granted_by_v77`;
- runtime / tool-use / product / external handoffs require matching
  later-authority refs;
- family closeout alignment lists `V77-A`, `V77-B`, and `V77-C` as the closed
  slice ladder without selecting `V78`;
- focused tests for the new `V77-C` package surface and export-schema parity
  pass;
- `make check` passes before any Python implementation PR is opened.

## Do Not Accept If

- authority posture rows reference unknown `V77-A` or `V77-B` rows;
- authority posture rows grant runtime permission or tool-use permission;
- summary rows omit blocking source, authority, telemetry, rollback, or target
  gaps;
- summary rows become ready while blockers remain;
- handoff rows perform runtime execution, tool use, product authorization,
  external branch activation, release, recursive policy amendment, or any
  later family;
- runtime / tool-use / product / external handoffs omit matching required
  later-authority refs;
- family closeout claims command execution, runtime permission grant, worker
  assignment, dispatch execution, product launch, release, external branch
  activation, benchmark truth, model selection, living-memory authority, or
  recursive policy amendment;
- family closeout selects `V78` or any later family as completed rather than
  future pressure.

## Local Gate

- for this docs-only starter bundle:
  - `make arc-start-check ARC=217`
- before any Python implementation PR:
  - `make check`
