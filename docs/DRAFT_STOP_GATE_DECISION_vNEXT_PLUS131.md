# Draft Stop-Gate Decision vNext+131

Status: proposed gate for `V44-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS131.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `packages/adeu_reasoning_assessment` scaffold exists and remains the
  only active `V44-A` package;
- `adeu_reasoning_template_probe@1` and `adeu_structural_reasoning_trace@1` export and
  mirror deterministically;
- canonical flat and hierarchical reference probes validate cleanly;
- canonical clean and lawful-blocked reference traces validate cleanly;
- reject fixtures fail closed for:
  - invalid early closure posture mismatch;
  - invalid hierarchical return-to-parent evidence;
- the released contracts keep blocked posture distinct from invalid early closure;
- no scoring, taxonomy, benchmark, or model-profile fields appear in the `V44-A`
  package surface;
- targeted tests cover schema export, canonical ids, deterministic fixture replay, and
  starter hierarchical trace law.

## Do Not Accept If

- the slice uses `V46` benchmark metrics or benchmark-family artifacts as if they were
  part of `V44-A`;
- the trace contract silently aggregates into normalized taxonomy or model-profile
  conclusions;
- hierarchical probes omit top-level plan-spine or return posture;
- blocked and invalid early closure are collapsed into one terminal status;
- the package widens into contest doctrine, runtime selection, or SRM architecture;
- root `spec/` mirrors are claimed in docs but missing from the released package lane.

## Local Gate

- run `make arc-start-check ARC=131`

