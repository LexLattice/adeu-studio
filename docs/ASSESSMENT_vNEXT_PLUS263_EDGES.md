# Assessment vNext+263 Edges

Status: pre-lock edge assessment for `PB-CASE-EXPANSION-0-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS263_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Case Expansion Could Become Benchmark Construction

- Risk:
  curated local cases could be read as representative ProgramBench coverage.
- Required containment:
  request rows must carry selection horizon, rationale, bias posture,
  diversity posture, dedupe policy, and
  `representativeness_posture = not_representative_benchmark_sample`.

### Edge 2: Duplicate Cases Could Launder As New Supply

- Risk:
  an existing released local case lineage could be relabeled as a new case.
- Required containment:
  candidate case ideas must carry candidate hashes, source subset hashes,
  existing-lineage overlap refs, nearest existing case refs, and novelty or
  duplication posture. Duplicates require explicit smoke/regression rationale.

### Edge 3: Source Pool Rows Could Expose Hidden Or Forbidden Material

- Risk:
  hidden tests, official evaluator output, original source facts, source
  lookup facts, decompilation facts, internet/external repo facts, or
  postmortem-only material could enter visible source pools.
- Required containment:
  source pool rows must carry source identity hashes, origin posture,
  visibility posture, store presence posture, derived summary policy, and
  allowed/exclusion posture. Forbidden sources cannot be allowed for
  expansion.

### Edge 4: Derived Summaries Could Launder Forbidden Evidence

- Risk:
  forbidden or auditor-only evidence could be transformed into visible labels,
  case ideas, behavior obligations, probe expectations, or oracle claims.
- Required containment:
  validators must enforce the named no-derived-summary-laundering law and
  reject hidden/forbidden names, paths, excerpts, test names, semantic
  summaries, hidden artifact identifiers, original-source clues, and derived
  facts in visible or blueprint-visible rows.

### Edge 5: Support-Only Context Could Become Eligibility

- Risk:
  support doctrine or advisory context could make a candidate case eligible
  without a cleanroom-visible source witness.
- Required containment:
  eligible candidate case ideas require at least one cleanroom-visible source
  witness. Support-only rows may remain context but cannot create eligibility
  alone.

### Edge 6: A Controls Could Grant Blueprint Or Execution Authority

- Risk:
  expansion controls could authorize blueprint creation, local execution,
  batch execution, scoring, baseline comparison, or model ranking.
- Required containment:
  A controls must keep blueprinting deferred to B and reject local execution,
  batch execution, scoring, baseline comparison, model ranking, official
  evaluator access, source lookup, decompilation, internet lookup, Docker
  socket, host secrets, wider write scope, hidden-test access, and
  future-family selection.

### Edge 7: A Could Prematurely Emit B/C Artifacts

- Risk:
  A could ship case blueprints, evidence packs, probe contracts, oracle
  boundaries, contamination screens, lineage registration, readiness summary,
  handoff, or closeout rows.
- Required containment:
  A fixtures and validators must reject `PB-CASE-EXPANSION-0-B/C` artifact
  kinds.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus263/`.
- The implementation PR must run the focused `PB-CASE-EXPANSION-0-A` tests
  and `make check` before opening the PR.
- Later `PB-CASE-EXPANSION-0-B` must bind behavior obligations to source
  witnesses and keep probe contracts plan-only.
- Later `PB-CASE-EXPANSION-0-C` must keep ready counts inventory-only and
  handoffs pressure-only.

## Current Judgment

The `PB-CASE-EXPANSION-0-A` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=263` passes.
