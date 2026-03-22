# Assessment vNext+75 Edges

Status: planning-edge assessment for `V39-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS75_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Plan / Execution Collapse

- Risk:
  the first released fix-plan lane could be misread as already authorizing diffs,
  autofix execution, or direct repo mutation.
- Response:
  keep `V39-D` advisory-only and forbid any direct mutation authority or patch payload
  in the artifact.

### Edge 2: Role-Collapse Drift

- Risk:
  forward-agent prevention guidance and post-optimizer corrective guidance could be
  merged into one generic advice list and erase the distinct agent roles.
- Response:
  require structurally separate forward-agent and post-optimizer projection surfaces in
  the canonical artifact.

### Edge 3: Source-Finding Blur

- Risk:
  projected items could bind only to a rule id or loose locator and lose exact
  traceability back to one released source finding or source candidate.
- Response:
  require every projected item to carry a stable `source_finding_id` or equivalent
  exact source item identity derived from the released conformance lane.

### Edge 4: Registry / Report Bypass

- Risk:
  the plan lane could bypass the released registry or released conformance report and
  synthesize planning directly from raw subjects or ad hoc heuristics.
- Response:
  require the fix plan to consume released `V39-B` and `V39-C` artifacts directly and
  fail closed when source bindings are missing or inconsistent.

### Edge 5: Safe-Autofix Overclaim

- Risk:
  the plan lane could smuggle broader rewrite authority by treating any finding as if
  it were eligible for safe autofix planning.
- Response:
  restrict safe-autofix planning to findings already surfaced as released
  `safe_autofix_candidates` by `V39-C`.

### Edge 6: No-Op Suppression

- Risk:
  the first released plan lane could force action even when the source report carries
  zero findings or when findings exist but none are plannable in this slice.
- Response:
  require one valid no-op / no-finding fix-plan fixture and explicit acceptance of
  empty projected-item sets.

### Edge 7: Score / Priority Creep

- Risk:
  the fix plan could introduce hidden weighted priority or urgency scoring that later
  becomes policy by inertia.
- Response:
  keep the plan anti-score by construction and forbid hidden scalar prioritization or
  merge-worthiness outputs.

### Edge 8: Policy Reinvention

- Risk:
  the projection lane could silently become a second policy authoring surface and emit
  role guidance that contradicts the released registry policy.
- Response:
  require projected role guidance to summarize or select from released policy only and
  reject contradictory role guidance.

### Edge 9: Oracle-Lane Leakage

- Risk:
  carried-through `resolution_route` metadata could be misread as proof that hybrid
  adjudication already exists.
- Response:
  preserve the descriptive-only status of `resolution_route` and reserve any
  checkpoint execution for `V39-E`.

### Edge 10: Authorship Regression

- Risk:
  once the lane starts emitting planning guidance, it could slide back into
  “AI-looking code” rhetoric instead of pressure-mismatch governance.
- Response:
  keep authorship/origin absent from the fix plan schema, derivation logic, fixtures,
  and tests.

## Current Judgment

- `V39-D` is worth implementing now because `V39-C` is now released on `main` and the
  family needs a typed role-separated planning surface before it can responsibly widen
  into hybrid adjudication or any future execution lane.
