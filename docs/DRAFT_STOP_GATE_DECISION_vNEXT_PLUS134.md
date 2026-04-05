# Draft Stop-Gate Decision vNext+134

Status: proposed gate for `V44-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS134.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the repo-owned `packages/adeu_reasoning_assessment` surface remains the only active
  `V44-D` package;
- one released `adeu_reasoning_probe_suite@1` exports and mirrors deterministically;
- suite membership semantics are carried as first-class released member records, not
  only as external matrix prose;
- released `V44-A` probes/traces plus released `V44-B` and `V44-C` consumers are used
  as-is, with no semantic redefinition;
- the widened suite covers all four starter template classes deterministically:
  - `lane_preserving_decomposition`
  - `branching_under_uncertainty`
  - `local_repair_continuation`
  - `invariance_under_surface_variation`;
- at least one released suite member exists for each starter template class;
- invariance probes preserve explicit procedure anchors under only:
  - `paraphrase_preserving`
  - `presentation_shift_preserving`;
- at least one positive released invariance member exists for each frozen
  surface-variation kind;
- local-repair probes keep repair locality bounded to `local_only`;
- member-level consumer compatibility remains explicit and deterministic, including:
  - taxonomy-only compatibility where applicable;
  - differential compatibility only where pair compatibility is already lawful;
- ordering and `suite_hash` law are frozen over the ordered canonical suite form;
- reject fixtures fail closed for:
  - invalid procedure-preservation anchors;
  - non-local repair rewrite posture;
- no profile, benchmark, or recursive-depth fields appear in the `V44-D` package
  surface;
- targeted tests cover deterministic suite ids/hashes, template-class widening, suite
  matrix replay, and released consumer compatibility replay.

## Do Not Accept If

- the widened library silently redefines released `V44-B` taxonomy or released
  `V44-C` differential semantics;
- the suite contract relies on blanket suite-level compatibility claims instead of
  member-level compatibility posture;
- answer equivalence is used as a substitute for explicit procedure-preservation
  anchors;
- repair-locality law is weakened into global rewrite permissiveness;
- recursive-depth or nested-grandchild probes enter the starter slice;
- model-profile, ranking, or benchmark doctrine appears in the released contract;
- root `spec/` mirrors are claimed in docs but missing from the released package lane.

## Local Gate

- run `make arc-start-check ARC=134`
