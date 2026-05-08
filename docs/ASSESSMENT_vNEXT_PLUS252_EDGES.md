# Assessment vNext+252 Edges

Status: closeout-edge assessment for `PB-ATTEMPT-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Attempt Law

- Closeout containment:
  invocation, output capture, materialization, and sandbox trace rows bind to
  released attempt request, worker input packet, dispatch preflight, and
  non-authority guardrail refs before bundle validation succeeds.
- Result:
  pass.

### Edge 2: Blocked Preflight Could Still Produce Invocation Rows

- Closeout containment:
  worker invocation records cannot validate unless the released A dispatch
  preflight is passed for later local attempt review.
- Result:
  pass.

### Edge 3: Multiple Invocations Could Hide Retries

- Closeout containment:
  worker invocation records require `attempt_invocation_index = 1`; retry
  parent and retry authority rows remain unselected.
- Result:
  pass.

### Edge 4: Invocation Could Drift From The Preflighted Input Packet

- Closeout containment:
  invocation records require input packet hash, worker-visible context hash,
  tool manifest ref, allowed tool manifest hash, and forbidden tool manifest
  hash.
- Result:
  pass.

### Edge 5: Invocation Could Use Hidden, Source, Internet, Or Secret Channels

- Closeout containment:
  invocation and sandbox trace rows reject hidden-test access, source lookup,
  internet lookup, decompilation, external repo access, Docker socket access,
  host-secret access, and official runner/evaluator contact.
- Result:
  pass.

### Edge 6: Worker Output Could Launder Forbidden Content

- Closeout containment:
  output capture requires forbidden-content screening posture; non-passing
  screening blocks candidate materialization; blocked top-level screening
  postures require matching blocked-row evidence.
- Result:
  pass.

### Edge 7: Bounded Excerpts Could Replace Output Hashes

- Closeout containment:
  every captured output row requires exactly one output hash and one bounded
  excerpt row.
- Result:
  pass.

### Edge 8: Candidate Materialization Could Use Unscreened Output Bytes

- Closeout containment:
  materialization input hash must match the screened
  `worker_declared_candidate_file` output hash, and the output capture must
  contain exactly one such candidate-file row.
- Result:
  pass.

### Edge 9: Candidate Materialization Could Escape Released Write Scope

- Closeout containment:
  materialization rows require write-scope ref, write-scope attestation,
  materialization input hash, materialization output manifest hash, generated
  file hashes, and `materialized_inside_write_scope = true`.
- Result:
  pass.

### Edge 10: Sandbox Trace Could Become Official Execution Or Evaluation

- Closeout containment:
  sandbox application traces describe local sandbox application only and
  cannot claim official ProgramBench execution, official evaluator contact,
  hidden-test equivalence, benchmark score, model ranking, or official
  submission.
- Result:
  pass.

### Edge 11: Candidate Materialization Could Become Official Submission

- Closeout containment:
  candidate materialization requires local-only posture, no official
  submission posture, and no benchmark truth posture.
- Result:
  pass.

### Edge 12: B Could Prematurely Emit C Artifacts

- Closeout containment:
  B emitted only invocation record, output capture, candidate materialization,
  and sandbox application trace shapes.
- Result:
  pass.

### Edge 13: B Rows Could Select Future Family Or Rank Models

- Closeout containment:
  invocation and materialization rows carry no future-family selection,
  benchmark score, leaderboard, or model-ranking authority.
- Result:
  pass.

## Residual Edges

- `PB-ATTEMPT-0-C` must consume released `PB-ATTEMPT-0-A` and
  `PB-ATTEMPT-0-B` refs before exporting workbench evidence, reviewing attempt
  results, queuing remand pressure, or closing the family.
- `PB-ATTEMPT-0-C` must bind any workbench evidence export to released
  `PB-RECON-0` validator bindings and validation result refs so attempt output
  cannot launder itself into accepted workbench evidence.
- `PB-ATTEMPT-0-C` must gate `attempt_locally_accepted` on exported
  `PB-RECON-0` local-accepted summaries and must fail closed on contamination,
  sandbox violations, export gaps, hidden-test equivalence, official
  submission posture, or missing validator results.
- `PB-ATTEMPT-0-C` remand queues must carry local retry pressure only and must
  not become retry authority or use hidden-test, official evaluator,
  original-source, decompilation, internet, or external-repo facts.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, broader benchmark
  result governance, product, graph, release, or recursive-policy work remain
  unselected.

## Current Judgment

- `PB-ATTEMPT-0-B` is closed on `main` as a bounded invocation-capture slice.
- `PB-ATTEMPT-0` remains open for `PB-ATTEMPT-0-C`; no family closeout has
  occurred.
- The shipped slice preserves the intended attempt membrane: it records one
  local worker invocation, bounded worker output capture, screened local
  candidate materialization, and sandbox application trace evidence, but it
  does not export workbench evidence, review the attempt result, queue remand,
  run official ProgramBench, expose hidden tests, claim benchmark truth, score
  benchmarks, rank models, create official submissions, transition runtime, or
  select a future family.
