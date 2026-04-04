# Draft Stop-Gate Decision (Pre vNext+126)

This note records the pre-start stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md`

Status: draft decision scaffold before implementation (April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS126.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v126_pre_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Closeout evidence, metrics, runtime observability, and final pass/fail posture will be written after implementation lands."
}
```

## Decision Guardrail

- This note is a pre-start scaffold only.
- It does not redefine `docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md`.
- It does not authorize release by itself.
- Final stop-gate judgment will require post-implementation evidence, targeted web
  tests, and refreshed closeout artifacts.

## Intended Decision Scope

The expected bounded decision for `vNext+126` is whether ADEU should accept the first
repo-owned `V51-C` browser/UI seam over the released `V51-A` kernel plus released
`V51-B` API stack, with:

- one bounded route only:
  - `/odeu-sim`
- one consumer posture over released `POST /odeu-sim/run` only;
- one admitted UI input set only:
  - `scenario_name`
  - `seed`
  - `steps`
- initial route posture only:
  - `idle`
  - defaults prefilled
  - user-triggered run
- fixed `summary_only_json` output mode only;
- one summary-render posture only:
  - meta
  - config snapshot
  - full `current_metric`
  - exact three-key `lane_summary`
  - sparse observed-only `action_counts`
  - event/evidence/sanction counts
- one typed route-status split only:
  - `idle`
  - `loading`
  - `completed_clean`
  - `fail_closed_invalid_request`
  - `fail_closed_kernel_mismatch`
- one exact route-status mapping law only:
  - before request:
    - `idle`
  - in-flight request:
    - `loading`
  - completed response:
    - map directly from released API `request_status`
- `response_hash` retained in the emitted view-model only;
- no direct kernel imports into `apps/web`;
- no reset/step/start/pause controls, override sliders, network graph, event trace, or
  persistent browser state.

## Expected Evidence Before Closeout

Closeout should eventually point to:

- one merged PR implementing the bounded `V51-C` slice;
- green CI on that merged PR;
- route-smoke coverage for `/odeu-sim`;
- targeted web tests proving summary rendering for the admitted starter scenarios,
  typed failure rendering, deterministic minimal interaction behavior, and absence of
  forbidden control widening;
- refreshed stop-gate metrics and runtime-observability artifacts for `vNext+126`;
- one post-closeout assessment document capturing the surviving `V51-C` edges.

## Pre-Start Recommendation

Recommendation for this scaffold:

- `PROCEED_WITH_BOUNDED_V51C_IMPLEMENTATION`

Rationale:

- `V51-A` and `V51-B` are now released on `main`, so the next missing layer is the
  first bounded browser/UI consumer rather than more kernel or API work;
- the imported prototype's interactive browser sandbox is useful shaping evidence, but
  the repo should internalize one summary-first web route before any richer controls;
- the lock for `vNext+126` keeps the UI seam subordinate to the released API contract,
  freezes the bounded request/rendering posture, and blocks prototype-style control
  widening in the same move.
