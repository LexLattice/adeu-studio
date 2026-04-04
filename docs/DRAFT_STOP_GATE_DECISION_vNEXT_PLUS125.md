# Draft Stop-Gate Decision (Pre vNext+125)

This note records the pre-start stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md`

Status: draft decision scaffold before implementation (April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS125.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v125_pre_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Closeout evidence, metrics, runtime observability, and final pass/fail posture will be written after implementation lands."
}
```

## Decision Guardrail

- This note is a pre-start scaffold only.
- It does not redefine `docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md`.
- It does not authorize release by itself.
- Final stop-gate judgment will require post-implementation evidence, committed
  fixtures, targeted tests, and refreshed closeout artifacts.

## Intended Decision Scope

The expected bounded decision for `vNext+125` is whether ADEU should accept the first
repo-owned `V51-B` API seam over the released `V51-A` kernel, with:

- one bounded route only:
  - `POST /odeu-sim/run`
- one stateless non-persistent execution posture only;
- one summary-only JSON response mode only;
- one admitted request field set only:
  - `scenario_name`
  - `seed`
  - `steps`
  - `output_mode`
- one released stateless helper path only:
  - `run_canonical_scenario(...)`
- one released summary-helper projection path only:
  - `summarize_lane_state(...)`
  - `summarize_action_counts(...)`
- one typed fail-closed outcome split only:
  - `completed_clean`
  - `fail_closed_invalid_request`
  - `fail_closed_kernel_mismatch`
- non-negative `seed` and bounded `steps` validation only;
- one summary payload with explicit:
  - `meta`
  - `config_snapshot`
  - full `current_metric`
  - exact three-key `lane_summary`
  - sparse observed-only `action_counts`
  - event/evidence/sanction counts
- frozen `request_hash` / `response_hash` subjects only;
- no scenario overrides, mutable reset/step/state session, browser UI, static surface,
  or persistent storage.

## Expected Evidence Before Closeout

Closeout should eventually point to:

- one merged PR implementing the bounded `V51-B` slice;
- green CI on that merged PR;
- deterministic `v51b` response fixtures for the admitted starter scenarios;
- targeted API tests proving deterministic replay, fail-closed invalid-request
  handling for unsupported scenario names, negative seeds, and invalid step counts,
  fail-closed kernel-stack mismatch handling, stateless helper-path usage, and absence
  of persistent session widening;
- refreshed stop-gate metrics and runtime-observability artifacts for `vNext+125`;
- one post-closeout assessment document capturing the surviving `V51-B` edges.

## Pre-Start Recommendation

Recommendation for this scaffold:

- `PROCEED_WITH_BOUNDED_V51B_IMPLEMENTATION`

Rationale:

- `V51-A` is now released on `main`, so the next missing layer is the first bounded
  API consumer rather than another kernel slice;
- the imported prototype's mutable reset/step/state API is useful shaping evidence,
  but the repo should internalize only one stateless route first;
- the lock for `vNext+125` keeps the API seam subordinate to the released stateless
  kernel helper path, freezes exact response projection/hash law, and blocks
  UI/persistence widening in the same move.
