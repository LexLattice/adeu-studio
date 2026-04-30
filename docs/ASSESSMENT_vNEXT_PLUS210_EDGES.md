# Assessment vNext+210 Edges

Status: pre-lock edge assessment for `V75-B` (May 1, 2026 UTC).

Authority layer: planning / pre-start scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS210_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Assignment Plan Could Become Dispatch

- Containment:
  assignment rows must use `assignment_execution_posture =
  no_execution_authorized` and reference released `V75-A` guardrails.
- Required proof:
  reject fixture for assignment-as-execution.

### Edge 2: Worker Role Could Become Permission Grant

- Containment:
  role profiles describe capacity only; allowed tools are applicability cues,
  not run permission.
- Required proof:
  reject fixture for role profile treated as permission.

### Edge 3: Worker Output Could Become Truth

- Containment:
  IO contracts must mark expected outputs as review-only, reconciliation
  required, adversarial-review required, human-ratification required, or not
  truth.
- Required proof:
  reject fixture for output-as-truth.

### Edge 4: Tool Applicability Could Become Global Scope

- Containment:
  tool matrix rows must be target-bound and horizon-bound.
- Required proof:
  reject fixture for global tool applicability or tool-run permission.

### Edge 5: Upstream Exceptions Could Be Dropped

- Containment:
  upstream `V75-A` carried exceptions and later-authority blockers must be
  represented in the dispatch exception register or explicitly marked not
  applicable with source evidence.
- Required proof:
  reject fixture for omitted upstream exception.

### Edge 6: External Branch Worker Could Activate V43

- Containment:
  `external_branch_review_worker` remains blocked or future-family-only unless
  `V43` branch posture source refs are present.
- Required proof:
  reject fixture for external branch worker planning without `V43` source.

### Edge 7: V75-B Could Begin V75-C

- Containment:
  worker output reconciliation plan, dispatch reconciliation contract,
  post-dispatch-review handoff, and family closeout alignment remain deferred.
- Required proof:
  closeout evidence records all `V75-C` selections as false.

### Edge 8: Runtime/Product/Release Authority Could Be Laundered

- Containment:
  assignment, role, IO, tool, and exception rows must not grant runtime,
  product, release, external, benchmark, model-selection, living-memory, or
  recursive-policy authority.
- Required proof:
  reject fixtures for downstream authority claims.

## Residual Edges

- `V75-C` must later define reconciliation and post-dispatch-review handoff
  without claiming dispatch execution or worker-output truth.
- Runtime permission and effect envelopes remain unselected future territory.
- Productized typed adjudication remains visible but non-authorizing.
- External contest participation and `V43` activation remain conditional
  future branches.

## Pre-Lock Judgment

- `V75-B` is appropriately scoped as bounded worker orchestration planning.
- The starter may create role, assignment-plan, IO, tool-applicability, and
  exception substrate only.
- The highest-risk seams are assignment-as-execution, role-as-permission,
  output-as-truth, tool-as-global-scope, exception omission, and external
  branch activation.
