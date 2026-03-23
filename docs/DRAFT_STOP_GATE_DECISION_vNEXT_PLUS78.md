# Draft Stop-Gate Decision vNext+78

Status: proposed gate for `V40-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- deterministic compiler entrypoints consume the released `V40-A` semantic-root
  artifacts without redefining them;
- `packages/adeu_architecture_compiler` is the only newly activated package in this
  slice;
- canonical `adeu_architecture_conformance_report@1` validates and exports cleanly;
- the conformance report carries deterministic consumed-root lineage for the exact
  released inputs it evaluated;
- stable deterministic `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and `ASIR-P` check-id
  families are emitted;
- whole-ASIR integrity and section-local validation fail closed on required violations;
- blocked vs ready gating is explicit and deterministic;
- `human_escalation_refs` remains static deterministic escalation lineage only;
- `emitted_artifact_refs` remains empty in this slice;
- Python tests cover:
  - schema/model validation,
  - schema export parity,
  - deterministic conformance replay,
  - fail-closed integrity checks,
  - blocked vs ready gating.

## Do Not Accept If

- `V40-B` bypasses released root-family artifacts with free-floating hybrid or
  projection fixtures;
- `packages/adeu_architecture_ir` root semantics are silently redefined in the compiler
  package;
- `projection_readiness = ready` is emitted despite blocking ambiguity or failed
  required checks;
- `projection_readiness = ready` is emitted despite non-empty
  `human_escalation_refs`;
- the conformance report is used to smuggle checkpoint, oracle, projection manifest, or
  lowering state into the slice;
- `human_escalation_refs` points at hybrid or checkpoint artifacts that do not belong
  to `V40-B`;
- `ASIR-H-xxx` or any hybrid artifacts are shipped in `vNext+78`;
- `ASIR-P-xxx` is widened to imply manifest-integrity checks that belong to later
  projection slices;
- authoritative and mirrored schema exports drift.

## Local Gate

- run `make arc-start-check ARC=78`
