# Assessment vNext+74 Edges

Status: planning-edge assessment for `V39-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS74_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Registry Bypass

- Risk:
  the observation/report lane could quietly redefine `V39-B` vocabularies or drift
  away from the released registry contract.
- Response:
  require all findings to bind released registry rule ids and consume the released
  registry fixture/schema directly, and require any carried-through finding metadata
  to match the referenced released registry rule exactly.

### Edge 2: Detector Overclaim

- Risk:
  the slice could claim execution of contextual, ambiguous, or meta-governance rules
  as if they were deterministic.
- Response:
  keep first execution bounded to `evidence_regime = deterministic_local` only and
  fail closed for everything else.

### Edge 3: Observation/Report Collapse

- Risk:
  packet-level finding evidence could collapse into report-level summary language and
  hide what was actually observed.
- Response:
  keep observation packets concrete and reports explicitly aggregated from those
  packets rather than generated as free prose.

### Edge 4: Score Creep

- Risk:
  the conformance report could introduce a scalar pressure-mismatch score that later
  becomes policy by inertia.
- Response:
  keep any posture field convenience-only and forbid numeric merge-worthiness outputs.

### Edge 5: Subject Drift

- Risk:
  subject references could become unstable, non-local, or network-dependent.
- Response:
  bind the first released subject inputs to committed local fixtures and deterministic
  subject provenance only, and keep each `V39-C` observation packet single-subject.

### Edge 6: Repo-Wide Scan Leakage

- Risk:
  the first released observation lane could quietly widen into a repo crawler rather
  than a bounded local fixture-driven baseline.
- Response:
  keep `V39-C` fixture-driven and local-subject-only in the first slice.

### Edge 7: Fix-Plan Leakage

- Risk:
  findings could be coupled directly to rewrite plans or mutation surfaces before
  `V39-D` exists.
- Response:
  keep `V39-C` bounded to observation and reporting only; defer fix plans entirely.

### Edge 8: Oracle-Lane Leakage

- Risk:
  carried-through `resolution_route` metadata could be misread as proof that hybrid
  adjudication already exists.
- Response:
  preserve the descriptive-only status of `resolution_route` and reserve any
  checkpoint execution for `V39-E`.

### Edge 9: Positive-Only Fixture Bias

- Risk:
  the first released fixtures could show only positive detections and fail to prove
  both valid zero-finding replay and fail-closed behavior on unsupported execution.
- Response:
  require one valid no-finding packet/report case and one rejected unsupported
  execution case in the released fixtures and tests.

### Edge 10: Duplicate-Finding Inflation

- Risk:
  repeated copies of the same finding identity could inflate packet/report outputs and
  silently distort conformance summaries.
- Response:
  reject exact duplicate finding identity tuples inside one packet while still
  allowing repeated `rule_id` use when each finding has a distinct bounded local
  observation locator.

### Edge 11: Authorship Regression

- Risk:
  once concrete findings appear, the lane could slide back into “AI-looking code”
  rhetoric instead of pressure-mismatch governance.
- Response:
  keep authorship/origin absent from the packet, report, detector logic, and tests.

## Current Judgment

- `V39-C` is worth implementing now because `V39-B` is now released on `main` and the
  family needs a typed observed-finding lane before it can responsibly widen into
  fix-plan projection or hybrid adjudication.
