# Assessment vNext+218 Edges

Status: planning-edge assessment for `V78-A`.

Authority layer: pre-lock assessment, not closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS218_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Authority Request Could Become Authority Grant

- Risk:
  runtime execution authority requests could be overread as bounded authority
  decisions.
- Response:
  `V78-A` selects request, source index, and non-action guardrail only. It
  must reject authority decisions and all `V78-B` surfaces.

### Edge 2: Authority Grant Language Could Imply Execution

- Risk:
  later slices may use grant language that readers treat as command execution
  or live runtime permission.
- Response:
  `V78-A` must preserve `execution_posture =
  no_execution_performed_by_v78` and `tool_invocation_posture =
  no_tool_invocation_performed_by_v78`; `V78-B` grant-like rows remain
  later-review-only.

### Edge 3: Required Authority Could Become Free Text

- Risk:
  required authority source refs could become an untyped prose bucket.
- Response:
  `V78-A` uses embedded authority requirement rows with `authority_kind`,
  `required_for_horizon`, source refs, source-presence posture, and authority
  gap posture.

### Edge 4: Support Sources Could Become Eligibility

- Risk:
  roadmap, dogfood, or review docs could be treated as sufficient authority
  eligibility sources.
- Response:
  context rows may explain `V78`, but eligible runtime authority requests must
  cite released `V77-C` source rows and guardrails.

### Edge 5: Command Preflight Could Become Command Scope

- Risk:
  command preflight plus target refs from `V77-B` could be treated as command
  scope authorization.
- Response:
  `V78-A` may cite preflight context but must not emit command-scope
  authorization boundaries. That surface belongs to `V78-B`.

### Edge 6: Local Command Output Could Become Authority Evidence

- Risk:
  a command run outside the lock could be cited as authority evidence.
- Response:
  local command output and passing tool results are not authority evidence
  unless a prior authorized source explicitly admits them.

### Edge 7: Product Or External Pressure Could Launder Runtime Authority

- Risk:
  product-pressure or external-branch rows could be routed as runtime
  authority-ready.
- Response:
  product rows remain product-blocked or future-product-review-routed, and
  external rows remain external-blocked or future-family-only unless concrete
  `V43` posture exists.

### Edge 8: V78-A Could Start V78-B Or V78-C Early

- Risk:
  starter rows could include authority decisions, tool-use permission
  envelopes, command-scope boundaries, exception registers, readiness
  summaries, handoffs, or closeout rows.
- Response:
  `V78-A` selects only request, source index, and non-action guardrail
  surfaces. Later slices require their own starter trios.

## Current Judgment

- `V78-A` is worth drafting now because `V77` closed runtime-permission review
  while preserving explicit runtime / tool-use authority pressure without
  granting authority or executing commands.
- The starter slice should stay authority-request / source-index /
  non-action-guardrail only: it can make required later authority visible, but
  it must not decide authority, authorize tool use, define command-scope
  authorization, execute, productize, release, activate external branches,
  dispatch, or select a later family.
