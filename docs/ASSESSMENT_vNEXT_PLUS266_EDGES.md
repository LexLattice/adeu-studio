# Assessment vNext+266 Edges

Status: pre-lock edge assessment for `PB-MATRIX-INCLUSION-0-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS266_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Inclusion Request Could Float Without Matrix Identity

- Risk:
  a request could list cases without binding to a concrete base matrix
  revision and proposed revision candidate.
- Required containment:
  A must require one released base matrix revision, one proposed revision
  candidate, base revision hash, proposed revision hash, prior membership
  manifest hash, proposed membership manifest hash, and revision delta hash.

### Edge 2: Ready Case Could Become Matrix Member Automatically

- Risk:
  a `PB-CASE-EXPANSION-0-C` ready lineage or handoff could be treated as
  direct matrix inclusion.
- Required containment:
  A may mark candidates recordable/eligible only. Amendment plans, inclusion
  decisions, and revision registrations remain deferred to B/C.

### Edge 3: Candidate Intake Could Lose Cleanroom Identity

- Risk:
  a candidate could be flattened to a lineage ref without probe, oracle,
  source-boundary, contamination, readiness, and handoff identity.
- Required containment:
  candidate rows must carry lineage registration refs, readiness refs,
  handoff refs, source boundary hash, probe contract hash, oracle boundary
  hash, contamination screen hash, and expansion closeout ref.

### Edge 4: Existing Matrix Member Could Be Re-Added

- Risk:
  a case already present in the base matrix could be admitted again under a
  new label.
- Required containment:
  dedupe status, duplicate refs, and prior matrix membership status must be
  explicit. Existing members cannot be eligible for addition unless
  replacement/update or allowed smoke/regression posture is declared.

### Edge 5: Inclusion Could Become Benchmark Construction

- Risk:
  inclusion eligibility could be read as representative benchmark sampling or
  benchmark denominator construction.
- Required containment:
  control contract must require non-representative posture,
  local-membership inventory posture, and
  `benchmark_denominator_posture = not_benchmark_denominator`.

### Edge 6: Inclusion Could Encode Performance Strategy

- Risk:
  A rationale rows could select cases because they are likely to pass,
  improve score, help a model, or represent a benchmark edge.
- Required containment:
  A must reject benchmark score, pass rate, baseline comparison,
  model-ranking, likely pass/fail, and leaderboard language.

### Edge 7: Control Contract Could Widen Matrix Conditions

- Risk:
  inclusion controls could widen worker/model profile, tool policy, probe
  basis, write scope, network posture, or source visibility while still
  claiming comparable matrix posture.
- Required containment:
  A must reject control widening unless explicitly marked
  non-comparable local accounting only, and even then it must not grant
  ranking or baseline authority.

### Edge 8: A Could Prematurely Emit B/C Artifacts

- Risk:
  A could ship amendment plans, inclusion decisions, revision registrations,
  result projections, matrix summaries, or execution surfaces.
- Required containment:
  A emits only inclusion request, candidate intake, eligibility review,
  control contract, and non-authority guardrail shapes.

## Residual Edges

- `PB-MATRIX-INCLUSION-0-B` must consume released A rows before producing
  amendment plans, case deltas, comparability deltas, contamination deltas, or
  inclusion decision records.
- `PB-MATRIX-INCLUSION-0-B` must keep inclusion decision basis in
  governance/accounting terms, not performance-selection terms.
- `PB-MATRIX-INCLUSION-0-B` must enforce no contamination transfer by summary.
- `PB-MATRIX-INCLUSION-0-C` must keep revision counts inventory-only and
  post-inclusion handoffs pressure-only.

## Current Judgment

The `PB-MATRIX-INCLUSION-0-A` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=266` passes.
