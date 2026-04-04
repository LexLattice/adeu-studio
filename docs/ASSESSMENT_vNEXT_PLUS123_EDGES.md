# Assessment vNext+123 Edges

Status: pre-lock edge assessment for `V50-C` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS123_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Artifact-Stack Laundering

- Risk:
  the session surface could rediscover scope or semantics ambiently from the repo
  instead of consuming the released manifest/census/coverage/audit stack.
- Planned Response:
  require one explicit released artifact stack only, enumerate the exact compatibility
  checks in the lock, and fail closed on mismatch.

### Edge 2: Reopening `V50-B` Independence

- Risk:
  the session layer could silently reinterpret or reopen the released `V50-B`
  semantic-independence posture.
- Planned Response:
  consume the released `explicit_independence_from_v49` posture as fixed upstream
  contract and do not relitigate it in `V50-C`.

### Edge 3: Renderer-Level Semantic Reinterpretation

- Risk:
  the new session renderer could drift into minting fresh per-symbol judgments or
  reinterpreting released `audit_status` / `confidence_band` values.
- Planned Response:
  allow rendering and summarization of released audit rows only and forbid the session
  layer from minting new semantic judgments.

### Edge 4: Write-Capable Drift

- Risk:
  a first session-helper seam could quietly widen into write-capable or runtime mutation
  behavior.
- Planned Response:
  freeze `read_only_helper_render` as the only admitted starter session mode and reject
  write-capable widening.

### Edge 5: Status Collapse Across Distinct Failures

- Risk:
  invalid config, unsupported mode/format, and true artifact mismatch could all be
  collapsed into one undifferentiated failure posture.
- Planned Response:
  keep `fail_closed_input_mismatch` separate from `fail_closed_invalid_config`.

### Edge 6: Non-Deterministic Rendering

- Risk:
  repeated runs over the same released artifact stack could emit different rendered
  output or exit-code posture.
- Planned Response:
  require byte-identical replay for the emitted session artifact and rendered output,
  and freeze `session_hash` over the full emitted session artifact including
  `rendered_output`.

### Edge 7: Consumer Prematurity

- Risk:
  direct CLI entrypoints, API/web, or repo-wide consumer surfaces could leak into the
  first session slice.
- Planned Response:
  keep `V50-C` bounded to package-local session/helper logic, deterministic fixtures,
  and targeted tests only, with no `cli.py` in this slice.

### Edge 8: Prototype CLI Precedent Laundering

- Risk:
  the imported prototype CLI sample could be copied into live paths or treated as
  released authority.
- Planned Response:
  keep the bundle support-only and re-author any live session/CLI surface in
  repo-native form.
