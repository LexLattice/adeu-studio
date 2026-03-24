# Draft Stop-Gate Decision vNext+79

Status: proposed gate for `V40-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS79.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the released `V40-A` semantic-root and released `V40-B` conformance surfaces are
  consumed explicitly and are not bypassed by free-floating checkpoint fixtures;
- canonical `adeu_architecture_oracle_request@1`,
  `adeu_architecture_oracle_resolution@1`,
  `adeu_architecture_checkpoint_trace@1`, and
  `adeu_architecture_ir_delta@1` schemas validate and export cleanly;
- the checkpoint classifier emits only:
  - `deterministic_pass`
  - `deterministic_fail`
  - `oracle_needed`
  - `human_needed`;
- final adjudication obeys only the frozen legal table:
  - `deterministic_pass -> resolved_pass`
  - `deterministic_fail -> resolved_fail`
  - `oracle_needed -> resolved_pass | resolved_fail | escalated_human`
  - `human_needed -> escalated_human`;
- oracle requests are emitted only for `oracle_needed` checkpoints and replay identity
  is pinned exactly enough for deterministic cache/replay checks;
- contradictory, inconclusive, or replay-mismatched oracle output fails closed into
  escalation rather than a false `resolved_pass` or `resolved_fail`;
- oracle output remains advisory only and cannot mint new authority, capability,
  boundary class, or widened scope;
- `adeu_architecture_ir_delta@1` remains proposal-only and bounded to already-existing
  or explicitly pre-authorized refs;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic classifier and adjudication law,
  - exact replay-identity enforcement,
  - one-round oracle enforcement,
  - fail-closed contradiction handling,
  - advisory-only oracle boundaries,
  - bounded `ir_delta` scope and authority guardrails.

## Do Not Accept If

- the hybrid lane silently redefines `V40-A` root semantics or `V40-B` conformance
  semantics;
- checkpoint traces imply compile readiness, lowering readiness, or emitted downstream
  surfaces by themselves;
- any hybrid artifact can be emitted without binding back to released semantic-root and
  conformance lineage;
- oracle output can directly mutate the repo, emit patch payloads, or widen authority;
- multiple oracle rounds become legal in the first baseline;
- `adeu_architecture_ir_delta@1` acts like an applied patch rather than a bounded
  proposal artifact;
- the slice ships projection bundles, manifests, `adeu_core_ir` lowerings, UX
  lowerings, or API/web workbench routes;
- the formal Lean sidecar becomes a hidden prerequisite for mainline hybrid validity.

## Local Gate

- for the starter bundle: run `make arc-start-check ARC=79`
- for eventual implementation: run `make check`
