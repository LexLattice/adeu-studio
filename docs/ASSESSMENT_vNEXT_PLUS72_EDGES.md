# Assessment vNext+72 Edges

Status: planning-edge assessment for `V39-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS72_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Historical Rewrite Risk

- Risk:
  the slice could describe imported work as if it had always satisfied the full
  repo-native ADEU pre-doc and lock sequence.
- Response:
  keep retrospective alignment explicit and preserve the difference between
  imported history and maintainer normalization.

### Edge 2: Structural Conformance Overclaim

- Risk:
  a module-conformance lane could overclaim by presenting structural checks as
  if they fully decide architectural merit, product value, or merge worthiness.
- Response:
  keep the first family bounded to structural conformance plus explicit
  maintainer follow-up fields.

### Edge 3: Code/Process Collapse

- Risk:
  the slice could merge code-alignment and meta-sequence-alignment into one
  label, losing the main lesson exposed by the poetry PR.
- Response:
  require separate reported dimensions and keep them independently inspectable.

### Edge 4: Surface-Truth Drift

- Risk:
  imported PRs could still overclaim shipped user-facing behavior when the code
  only adds internal utilities.
- Response:
  bind the accepted shipped scope to explicit reachable surfaces and fail closed
  when the claim does not match the code.

### Edge 5: Network-Dependent Canonicalization

- Risk:
  the conformance path could depend on live GitHub PR state, making canonical
  evaluation non-deterministic and non-replayable.
- Response:
  require committed or explicitly materialized local inputs for canonical
  evaluation, with the canonical subject defined as a localized snapshot bundle
  rather than the live PR object.

### Edge 6: Policy Frame Drift

- Risk:
  the report could be reproducible only inside a moving frame if policy inputs
  are described vaguely as "current repo policy sources" without pinned hashes
  and evaluator version.
- Response:
  require policy source paths, policy content hashes, and evaluator/tool version
  in canonical evidence.

### Edge 7: Observation/Judgment Collapse

- Risk:
  the slice could jump directly from contributor claim to maintainer judgment,
  hiding the intermediate observed surface facts that justify the correction.
- Response:
  require the three-layer scope model:
  - `claimed_scope`
  - `observed_reachable_surfaces`
  - `accepted_shipped_scope`

### Edge 8: Silent Precedent Grant

- Risk:
  imported work could become precedent-bearing by silence once it exists in repo
  history.
- Response:
  default precedent status to `non_precedent` unless a maintainer explicitly
  grants precedent-bearing status with a reason.

### Edge 9: Premature Generalization

- Risk:
  the first slice could widen too early into a generalized all-module scoring
  engine before the repo proves the reference lane on one imported
  contribution.
- Response:
  keep `V39-A` bounded to one reference contribution and one explicit
  retrospective-alignment baseline.

## Current Judgment

- `V39-A` is worth implementing now because imported external PRs are already a
  live repo reality, and the repo currently lacks a native, disciplined way to
  evaluate and normalize them without either over-forgiving process gaps or
  faking full ADEU-native provenance after the fact.
