# Draft Stop-Gate Decision vNext+132

Status: proposed gate for `V44-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS132.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `packages/adeu_reasoning_assessment` surface remains the only active
  `V44-B` package;
- `adeu_structural_failure_taxonomy@1` exports and mirrors deterministically;
- released `V44-A` probes and traces are consumed as-is, with no semantic redefinition;
- clean and blocked reference taxonomy fixtures validate cleanly;
- normalized hierarchy-aware failure fixtures validate cleanly for at least:
  - `plan_spine_drift`
  - `active_step_decomposition_failure`
  - `reintegration_failure`;
- reject fixtures fail closed for:
  - unsupported break-tag mapping;
  - blocked trace coerced into failure-family output;
- no profile, benchmark, or one-number score fields appear in the `V44-B` package
  surface;
- targeted tests cover deterministic taxonomy ids, event-order-first failure-family
  ordering, mapping-matrix replay, and blocked posture preservation.

## Do Not Accept If

- the slice uses `V46` benchmark metrics or benchmark-family artifacts as if they were
  part of `V44-B`;
- the taxonomy helper silently invents mappings not grounded in released `V44-A`
  structure or released starter fixture expectations;
- blocked and invalid early closure are collapsed into one failure-family posture;
- paired-condition or profile doctrine appears in the released contract;
- root `spec/` mirrors are claimed in docs but missing from the released package lane.

## Local Gate

- run `make arc-start-check ARC=132`
