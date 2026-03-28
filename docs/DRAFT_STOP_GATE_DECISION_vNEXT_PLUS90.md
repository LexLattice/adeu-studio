# Draft Stop-Gate Decision vNext+90

Status: proposed gate for `V42-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS90.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` schemas
  validate and export with authoritative/mirrored parity;
- observation and hypothesis artifacts bind to one released `adeu_arc_task_packet@1`
  with deterministic replay;
- observation frame exposes first-class ontology inventory surfaces rather than embedding
  ontology only in prose observations;
- observation entries preserve explicit direct-vs-derived typing plus evidence refs;
- derived observations remain structural and do not carry governing-transform/task-rule
  hypothesis claims;
- decomposition coverage is denominator-bound with explicit required dimensions and
  missing-dimension register;
- unresolved observations remain explicit rather than being silently dropped;
- hypothesis entries include explicit support refs, ambiguity register, claim posture,
  utility-pressure register, and non-committing working-hypothesis posture;
- bounded-search absence is not emitted as impossibility;
- mode/legal deontic admissibility posture is carried forward from released packet
  authority without solver-local recomputation;
- the slice emits no action proposal, rollout trace, scorecard, or competition-mode
  authority;
- fixture ladder includes at least one accepted deterministic case and rejected
  decomposition/entitlement violations;
- Python tests cover schema validation, deterministic replay, and the fail-closed rules
  above.

## Do Not Accept If

- observation/hypothesis outputs are authored against ambient state while claiming packet
  lineage;
- ontology decomposition is left implicit in observation prose without typed inventory
  surfaces;
- direct observation and derived inference are blended without typed distinction;
- derived observation entries carry candidate rule/transform claims that should be
  hypothesis content;
- decomposition coverage lacks explicit denominator/required-dimension basis;
- ambiguity is erased and hypotheses are emitted as settled by prose only;
- bounded-search absence is promoted to impossibility;
- ontology or observation fields smuggle hidden solver/action semantics;
- the slice widens into action proposal, rollout, scorecard, or competition-mode
  surfaces while claiming to be only `V42-B`;
- authoritative/mirrored schema parity for released artifacts is missing.

## Local Gate

- run `make arc-start-check ARC=90`
