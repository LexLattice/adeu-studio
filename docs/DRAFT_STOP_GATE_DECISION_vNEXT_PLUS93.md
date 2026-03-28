# Draft Stop-Gate Decision vNext+93

Status: proposed gate for `V42-E`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS93.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_scorecard_manifest@1` schema validates and mirrors to `spec/`
  byte-for-byte;
- scorecard manifests are lineage-bound to one released
  `V42-A`/`V42-B`/`V42-C`/`V42-D` chain;
- `scorecard_source_kind` is explicit and machine-checkable;
- authority posture is decomposed into explicit typed subfields and
  `scorecard_outcome_summary` is descriptive-only;
- `competition_mode_posture` is explicit and enum-bounded;
- local replay lineage and external replay authority refs are explicit and
  non-conflated;
- environment/session/competition-scope identity fields are explicit and valid;
- scorecard outputs carry settlement/claim-posture continuity from released upstream
  artifacts;
- fixtures and tests cover authority-class matrix posture:
  - local shadow only,
  - competition posture declared with no official scorecard,
  - official imported scorecard with valid basis refs;
- fixtures and tests fail closed on:
  - missing source-kind discriminator,
  - missing authority posture,
  - missing replay lineage or replay-authority separation,
  - local-as-official authority laundering,
  - leaderboard/competition overclaim from local-only evidence,
  - settlement-posture erasure,
  - submission/tournament/operator authority leakage.

## Do Not Accept If

- scorecard authority is implied by summary prose without explicit typed basis refs;
- scorecard source kind is ambiguous or missing;
- local-only evidence is laundered into leaderboard-readiness or competition-success
  claims;
- local replay lineage is represented as if it were external replay authority;
- scorecard outputs collapse settlement posture into certainty-only claims;
- direct online submission execution is introduced in this slice;
- tournament orchestration, API routes, or web operator surfaces are shipped inside the
  same arc;
- `V42-E` redefines released `V42-A` through `V42-D` semantics.

## Local Gate

- run `make arc-start-check ARC=93`
