# Assessment vNext+215 Edges

Status: planning-edge assessment for `V77-A`.

Authority layer: pre-lock assessment, not closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS215_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Runtime Review Could Become Runtime Permission

- Risk:
  runtime-permission review requests could be overread as permission grants.
- Response:
  require non-execution guardrails and reject rows that grant runtime
  permission, tool-use permission, command execution, worker assignment, or
  dispatch execution.

### Edge 2: Command Intent Could Become Command Execution

- Risk:
  command pressure or a command-like label could be treated as permission to
  run a command.
- Response:
  split `command_intent_kind` from `command_execution_posture` and require
  `no_execution_authorized` in starter reference rows.

### Edge 3: Support Sources Could Become Eligibility

- Risk:
  roadmap, dogfood, or review docs could be treated as sufficient runtime
  eligibility sources.
- Response:
  context rows may explain `V77`, but eligible runtime review requests must
  cite released `V76-C` source rows and guardrails.

### Edge 4: Product Or External Pressure Could Launder Runtime Authority

- Risk:
  product-pressure or external-branch rows could be routed as runtime-ready.
- Response:
  product rows remain product-blocked or future-product-review-routed, and
  external rows remain external-blocked or future-family-only unless concrete
  `V43` posture exists.

### Edge 5: Local Command Output Could Become Permission Evidence

- Risk:
  a command run outside the lock could be cited as runtime permission.
- Response:
  local command output is not permission evidence. `V77-A` may only record
  source-bound runtime-review pressure and guardrails.

### Edge 6: Tool Applicability Could Become Tool-Use Permission

- Risk:
  target-bound tool applicability from earlier families could be mistaken for
  permission to invoke a tool for effect.
- Response:
  guardrails carry `tool_use_not_authorized_by_v77`, and `V77-A` rejects
  tool-use permission.

### Edge 7: V77-A Could Start V77-B Or V77-C Early

- Risk:
  starter rows could include command preflight, effect envelopes, telemetry,
  rollback, authority posture, summary, handoff, or closeout rows.
- Response:
  `V77-A` selects only request, source index, and non-execution guardrail
  surfaces. Later slices require their own starter trios.

## Current Judgment

- `V77-A` is worth drafting now because `V76` has closed reconciliation /
  arbiter review on `main` and the combined `V68` through `V76` dogfood probe
  confirms that runtime permission remains unselected future pressure.
- The starter slice should stay request/source/guardrail only: it can make
  runtime-permission review pressure visible, but it must not perform
  preflight, define effect envelopes, grant authority, execute, productize,
  release, activate external branches, dispatch, or select a later family.
