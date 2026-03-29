# Draft Stop-Gate Decision vNext+97

This note is the start-phase stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md`

Status: draft decision note (pre-start scaffold, March 29, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS97.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail (Start-Phase)

- This document is pre-start scaffolding only for `vNext+97`.
- It does not override lock-level contract semantics from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md`.
- Any closeout truth claim must be backed by committed `v97` artifacts/tests/evidence
  and a post-closeout state transition in this decision note.
- `V42-G3` may consume released `V42-A`..`V42-G2` surfaces but may not redefine them.

## Accept When

- canonical `adeu_arc_three_puzzle_harness_record@1` is released with authoritative and
  mirrored schema parity;
- deterministic harness orchestration executes exactly three predeclared selected
  puzzles in canonical selection order;
- each puzzle run is bound to released `adeu_arc_reasoning_run_record@1` surfaces with
  required stage-occupation evidence posture retained;
- harness records contain exactly three canonical puzzle entries even when one or more
  runs end blocked/failed;
- harness-level identity and config chains remain coherent across
  bundle/register/puzzle/run refs and executable setup surfaces;
- per-puzzle downstream refs for local eval/scorecard/submission posture are explicit,
  and optional aggregate refs are consistent with per-puzzle entries;
- committed fixtures include one accepted record and fail-closed rejected cases for
  retrospective swap, order violation, duplicate identity, omitted-entry laundering,
  chain mismatch, config drift, missing sequence evidence, and aggregation contradiction;
- tests cover schema parity, deterministic replay of accepted fixture, and rejection
  paths for selection/order/identity/evidence contradictions.

## Do Not Accept If

- the harness runs any puzzle outside the frozen three-puzzle selection register;
- accepted outcomes allow retrospective swap or canonical-order drift;
- accepted outcomes mark harness completion while omitting one of the three required
  canonical puzzle entries;
- per-puzzle reasoning-run occupancy posture is dropped or treated as optional;
- cross-puzzle executable setup drift is left untyped;
- harness-level aggregation refs can contradict per-puzzle run entries and still pass;
- deterministic claims depend on fresh model re-execution rather than fixed emitted
  artifacts and fixed evidence;
- the slice widens into `V42-G4`, benchmark tournament execution, API/web operator
  surfaces, or generalized multi-agent orchestration.

## Local Gate

- docs scaffold gate: `make arc-start-check ARC=97`
- implementation PR gate: `make check`
