# Draft Stop-Gate Decision vNext+95

Status: proposed gate for `V42-G1`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS95.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_puzzle_input_bundle@1` validates and exports with authoritative/
  mirror schema parity;
- deterministic ingest/freeze replay over the accepted fixture yields identical puzzle
  identity hashes and bundle IDs on repeated runs;
- puzzle source-kind and provenance references are explicit for each selected puzzle;
- the initial cohort contains exactly three puzzles bound by a declared selection basis;
- rejected fixtures fail closed for:
  - missing provenance refs,
  - identity-hash mismatch,
  - retrospective puzzle swap against the predeclared selection register;
- Python tests cover schema validation, deterministic replay, parity checks, and the
  rejection matrix above.

## Do Not Accept If

- puzzle ingest relies on prompt-authored ambient selection without typed source binding;
- canonicalization permits non-deterministic puzzle ordering or identity hashing;
- declared puzzle selection can be changed post-hoc after observing outcomes;
- implementation widens into reasoning-run bridge (`V42-G2`) or multi-puzzle run harness
  execution (`V42-G3`);
- implementation redefines released `V42-A`..`V42-F` semantics instead of consuming them;
- benchmark tournament/API/web/generalized orchestration surfaces are introduced.

## Local Gate

- run `make arc-start-check ARC=95`
