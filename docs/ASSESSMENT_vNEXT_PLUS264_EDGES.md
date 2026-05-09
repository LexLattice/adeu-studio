# Assessment vNext+264 Edges

Status: pre-lock edge assessment for `PB-CASE-EXPANSION-0-B`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Could Bypass Released A Eligibility

- Risk:
  a blueprint could be created for a blocked or undeclared candidate case
  idea.
- Required containment:
  B must require released A refs and reject blueprints whose candidate case
  idea is not A-eligible.

### Edge 2: Blueprint Rows Could Widen Source Visibility

- Risk:
  blueprint source refs could include sources outside the A-allowed source
  set.
- Required containment:
  blueprint source refs must be a subset of released A allowed source refs,
  and every B bundle must preserve one `case_expansion_ref`.

### Edge 3: Behavior Obligations Could Become Unwitnessed Task Truth

- Risk:
  blueprint obligations could be asserted from labels or support-only context.
- Required containment:
  every behavior obligation requires a basis row binding it to concrete
  source witness refs, support kind, support strength, unresolved
  counterevidence refs, and limitation notes.

### Edge 4: Evidence Pack Could Launder Hidden Or Forbidden Detail

- Risk:
  hidden tests, official evaluator facts, original-source clues, source
  lookup facts, decompilation facts, internet/external repo facts, or
  postmortem-only material could enter cleanroom evidence rows.
- Required containment:
  evidence packs must enforce no-derived-summary laundering and reject
  hidden/forbidden names, paths, excerpts, test names, semantic summaries,
  hidden artifact identifiers, original-source clues, and derived facts.

### Edge 5: Probe Contract Could Become Command Authority

- Risk:
  planned probes could become raw shell commands or execution permission.
- Required containment:
  probe command shapes must be argv-based templates with execution deferred,
  and raw shell strings or command execution authority must be rejected.

### Edge 6: Oracle Boundary Could Become Official Task Truth

- Risk:
  local oracle expectations could be overread as official ProgramBench truth
  or hidden-test equivalence.
- Required containment:
  oracle rows must carry local-only posture and reject hidden-test
  equivalence, official evaluator equivalence, benchmark truth, and official
  task truth.

### Edge 7: Contamination Screen Could Mark Tainted Evidence Clean

- Risk:
  hidden, forbidden, postmortem-only, source-derived, evaluator-derived, or
  excluded-derived evidence could be marked clean.
- Required containment:
  contamination screens must fail closed and expose blocker refs without
  revealing forbidden content.

### Edge 8: B Could Prematurely Emit C Artifacts Or Execution Artifacts

- Risk:
  B could ship lineage registration, readiness, handoff, closeout, execution,
  or scoring surfaces.
- Required containment:
  B fixtures and validators must reject `PB-CASE-EXPANSION-0-C` artifact
  kinds, local trial execution, probe execution, batch execution, benchmark
  score, baseline comparison, model ranking, official ProgramBench authority,
  and future-family selection.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus264/`.
- The implementation PR must run the focused `PB-CASE-EXPANSION-0-B` tests
  and `make check` before opening the PR.
- Later `PB-CASE-EXPANSION-0-C` must require clean B contamination screens
  and complete B blueprint/evidence/probe/oracle rows before lineage
  registration.
- Later `PB-CASE-EXPANSION-0-C` must keep ready counts inventory-only and
  matrix handoffs pressure-only.

## Current Judgment

The `PB-CASE-EXPANSION-0-B` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=264` passes.
