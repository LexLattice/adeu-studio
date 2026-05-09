# Assessment vNext+264 Edges

Status: post-closeout edge assessment for `PB-CASE-EXPANSION-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Could Bypass Released A Eligibility

- Closeout state:
  contained.
- Evidence:
  B bundle validation requires the released A expansion request, source pool
  manifest, eligibility review, control contract, and non-authority
  guardrail. Blueprints for blocked or unknown candidate case ideas are
  rejected.

### Edge 2: Blueprint Rows Could Widen Source Visibility

- Closeout state:
  contained.
- Evidence:
  blueprint source refs must be a subset of the A allowed source refs and
  the selected A candidate source refs. Evidence source witnesses must match
  the blueprint source set.

### Edge 3: Behavior Obligations Could Become Unwitnessed Task Truth

- Closeout state:
  contained after review hardening.
- Evidence:
  every behavior obligation requires exactly one basis row. Basis rows must
  cite source witness refs that resolve in the evidence pack and whose
  witnessed obligation list includes the supported obligation.

### Edge 4: Evidence Pack Could Launder Hidden Or Forbidden Detail

- Closeout state:
  contained.
- Evidence:
  no-derived-summary laundering validators reject hidden/forbidden names,
  paths, excerpts, test names, semantic summaries, hidden artifact
  identifiers, original-source clues, source/evaluator/decompilation facts,
  and benchmark-like scoring language.

### Edge 5: Probe Contract Could Become Command Authority

- Closeout state:
  contained.
- Evidence:
  probe command rows are argv-shaped templates with execution deferred.
  Raw shell strings, shell metacharacters, and command execution authority
  are rejected.

### Edge 6: Oracle Boundary Could Become Official Task Truth

- Closeout state:
  contained after review hardening.
- Evidence:
  oracle boundaries carry local-only posture and reject hidden-test
  equivalence, official evaluator equivalence, and benchmark truth. Oracle
  basis rows must resolve their source witnesses against the cleanroom
  evidence pack.

### Edge 7: Contamination Screen Could Mark Tainted Evidence Clean

- Closeout state:
  contained.
- Evidence:
  contamination screens require clean status and clean verdict for B lineage
  candidates. Any hidden, forbidden, evaluator, decompilation/source-lookup,
  or non-clean contamination rows block clean screening.

### Edge 8: B Could Prematurely Emit C Artifacts Or Execution Artifacts

- Closeout state:
  contained.
- Evidence:
  B emits only blueprint, cleanroom evidence pack, probe contract, oracle
  boundary, and contamination screen shapes. Lineage registration, readiness,
  matrix handoff, family closeout, execution, scoring, ranking, official
  ProgramBench authority, and future-family selection remain deferred.

## Residual Edges

- `PB-CASE-EXPANSION-0-C` must require released A and B rows before lineage
  registration, readiness summary, matrix candidate handoff, or family
  closeout rows validate.
- `PB-CASE-EXPANSION-0-C` must require a complete B blueprint, evidence pack,
  probe contract, oracle boundary, and clean contamination screen before a
  local case lineage can be registered.
- `PB-CASE-EXPANSION-0-C` must keep ready counts inventory-only, denominator
  posture local to the expansion request, and representativeness explicitly
  non-benchmark.
- `PB-CASE-EXPANSION-0-C` must keep matrix candidate handoffs pressure-only
  and must not grant direct matrix inclusion, batch execution, benchmark
  scoring, model ranking, official participation, or future-family
  selection.

## Current Judgment

`PB-CASE-EXPANSION-0-B` is closed. The next bounded slice is
`PB-CASE-EXPANSION-0-C`.
