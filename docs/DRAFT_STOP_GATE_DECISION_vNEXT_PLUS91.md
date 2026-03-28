# Draft Stop-Gate Decision vNext+91

Status: proposed gate for `V42-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS91.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` schemas validate
  and export with authoritative/mirrored parity;
- action/rollout artifacts bind to one released task packet plus released observation and
  hypothesis frames with deterministic replay;
- each action proposal carries explicit deontic admissibility posture against released
  legal envelope;
- each action proposal carries explicit `proposal_status`, decision-basis fields, and
  utility posture fields;
- each action proposal carries structured expected-outcome surfaces plus an
  `expectation_surface_hash` anchored before rollout;
- rollout trace preserves deterministic step ordering with explicit proposal refs and
  observed outcome refs;
- rollout trace preserves explicit pre-step/post-step state lineage for committed steps;
- rollout trace carries explicit expectation-vs-outcome comparison;
- rollout trace expectation surfaces remain byte-identical to proposal-bound expectation
  identity (no post-hoc rewrite);
- settlement posture from `V42-B` remains explicit across action and rollout artifacts;
- blocked/deferred proposal posture is preserved without forced committed-action payloads;
- ambiguity-bearing tactical choice carries explicit alternative-action register posture;
- rollout success does not mint universal necessity claims without entitlement evidence;
- fixture ladder includes accepted deterministic replay and rejected admissibility/
  lineage/anti-laundering violations, including hidden utility/tactical opacity cases;
- Python tests cover schema validation, deterministic replay, and all fail-closed rules
  above.

## Do Not Accept If

- action/rollout outputs are authored against ambient state while claiming released
  lineage;
- action legality is inferred locally rather than carried from released legal envelope;
- proposal status/decision-basis/utility posture fields are missing while claiming
  hypothesis-guided action selection;
- expected-outcome surfaces are summary-only, missing structured fields, or missing from
  rollout comparison;
- rollout ordering is non-deterministic or proposal linkage is incomplete;
- rollout step pre-state/post-state lineage is missing;
- rollout expectation identity differs from the pre-action proposal expectation surface;
- settlement posture is silently dropped at action/rollout surfaces;
- blocked/deferred posture is overwritten with forced committed-action semantics;
- one successful rollout is promoted to universal necessity without explicit entitlement;
- scorecard/replay/competition authority appears in `V42-C` artifacts;
- authoritative/mirrored schema parity for released artifacts is missing.

## Local Gate

- run `make arc-start-check ARC=91`
