# Assessment vNext+263 Edges

Status: post-closeout edge assessment for `PB-CASE-EXPANSION-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS263_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Case Expansion Could Become Benchmark Construction

- Closeout state:
  contained.
- Evidence:
  request rows require selection horizon, rationale rows, bias posture,
  diversity posture, dedupe policy, max case count, and
  `representativeness_posture = not_representative_benchmark_sample`.

### Edge 2: Duplicate Cases Could Launder As New Supply

- Closeout state:
  contained.
- Evidence:
  candidate case idea rows carry candidate hashes, source subset hashes,
  existing lineage overlap refs, nearest existing case refs, and novelty or
  duplication posture. Duplicate existing lineages require explicit
  smoke/regression rationale.

### Edge 3: Source Pool Rows Could Expose Hidden Or Forbidden Material

- Closeout state:
  contained after review hardening.
- Evidence:
  source row validation checks both `source_kind` and
  `source_origin_posture` before allowing expansion evidence. Forbidden rows
  cannot permit derived summaries and cannot carry visible postures.

### Edge 4: Derived Summaries Could Launder Forbidden Evidence

- Closeout state:
  contained.
- Evidence:
  no-derived-summary laundering validators reject hidden/forbidden names,
  paths, excerpts, test names, semantic summaries, hidden artifact
  identifiers, original-source clues, and derived facts in visible or
  blueprint-visible rows.

### Edge 5: Support-Only Context Could Become Eligibility

- Closeout state:
  contained after review hardening.
- Evidence:
  support context source rows require support-only visibility and
  `support_only_not_sufficient` exclusion reason. Eligible candidate case
  ideas require at least one cleanroom-visible source witness.

### Edge 6: Manifest Summary Rows Could Drift From Source Row State

- Closeout state:
  contained after review hardening.
- Evidence:
  forbidden, blocked, auditor-only, and support-only manifest summary refs
  must exactly match row classifications rather than merely containing a
  subset.

### Edge 7: Eligibility Warnings Could Become Orphan Top-Level Claims

- Closeout state:
  contained after review hardening.
- Evidence:
  carried blockers and carried warnings must resolve to candidate eligibility
  row blocker or warning refs.

### Edge 8: A Controls Could Grant Blueprint Or Execution Authority

- Closeout state:
  contained.
- Evidence:
  control and guardrail rows reject blueprint authority beyond later B
  review, local execution, batch execution, scoring, baseline comparison,
  model ranking, official evaluator access, source lookup, decompilation,
  internet lookup, Docker socket, host secrets, wider write scope,
  hidden-test access, trial execution, and future-family selection.

### Edge 9: A Could Prematurely Emit B/C Artifacts

- Closeout state:
  contained.
- Evidence:
  A emits only expansion request, source pool manifest, eligibility review,
  control contract, and non-authority guardrail shapes. Blueprints, evidence
  packs, probe contracts, oracle boundaries, contamination screens, lineage
  registrations, readiness summaries, handoffs, and family closeout remain
  deferred.

## Residual Edges

- `PB-CASE-EXPANSION-0-B` must consume released A rows before producing a
  blueprint, evidence pack, probe contract, oracle boundary, or contamination
  screen.
- `PB-CASE-EXPANSION-0-B` must bind behavior obligations to source witnesses
  and keep source witness support strength visible instead of treating
  witness presence as task truth.
- `PB-CASE-EXPANSION-0-B` must keep local oracle boundaries local-only and
  must not claim hidden-test equivalence, official evaluator equivalence, or
  benchmark truth.
- `PB-CASE-EXPANSION-0-B` must keep probe contracts plan-only, argv-shaped,
  and non-executing.
- `PB-CASE-EXPANSION-0-C` must keep ready counts inventory-only and handoffs
  pressure-only.

## Current Judgment

`PB-CASE-EXPANSION-0-A` is closed. The next bounded slice is
`PB-CASE-EXPANSION-0-B`.
