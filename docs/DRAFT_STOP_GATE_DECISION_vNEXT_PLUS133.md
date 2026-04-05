# Draft Stop-Gate Decision vNext+133

Status: proposed gate for `V44-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS133.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `packages/adeu_reasoning_assessment` surface remains the only active
  `V44-C` package;
- `adeu_structural_reasoning_differential@1` exports and mirrors deterministically;
- released `V44-A` probes/traces and released `V44-B` taxonomy artifacts are consumed
  as-is, with no semantic redefinition;
- reference starter pairs validate deterministically for at least:
  - `knowledge_deficit_supported`
  - `procedural_discipline_deficit_supported`
  - `mixed_or_ambiguous`
  - `paired_condition_insufficient`;
- reject fixtures fail closed for:
  - incompatible paired-condition compatibility posture;
  - missing required starter condition role;
- no profile, benchmark, or one-number score fields appear in the `V44-C` package
  surface;
- targeted tests cover deterministic differential ids, trace-qualified supporting
  evidence refs, pair compatibility replay, starter judgment mapping, and
  insufficient-pair posture.

## Do Not Accept If

- the slice uses `V46` benchmark metrics or benchmark-family artifacts as if they were
  part of `V44-C`;
- the differential helper silently invents pair semantics not grounded in released
  `V44-A` compatibility posture or released `V44-B` taxonomy surfaces;
- the differential helper emits unqualified event indexes that do not identify which
  condition trace supplied the evidence;
- incompatible or incomplete pairs are silently promoted into strong diagnosis;
- complete/incomplete/incompatible pair status is not mechanically coupled to the
  admitted judgment vocabulary;
- model-profile or model-ranking doctrine appears in the released contract;
- root `spec/` mirrors are claimed in docs but missing from the released package lane.

## Local Gate

- run `make arc-start-check ARC=133`
