# Assessment vNext+249 Edges

Status: closeout-edge assessment for `PB-RECON-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS249_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Workbench Law

- Closeout containment:
  B bundle validation consumes the released work order, worker context,
  exclusion manifest, sandbox policy, run budget, and guardrail refs before
  accepting local evidence rows.
- Result:
  pass.

### Edge 2: Candidate Artifact Could Become Official Submission

- Closeout containment:
  candidate artifact manifests require local workbench artifact posture and
  no official submission or official ProgramBench participation posture.
- Result:
  pass.

### Edge 3: Candidate Artifact Could Escape Sandbox Write Scope

- Closeout containment:
  generated file `write_scope_ref` values must resolve inside the released
  sandbox policy `allowed_write_scope_refs`.
- Result:
  pass.

### Edge 4: Candidate Artifact Hash Evidence Could Be Ambiguous

- Closeout containment:
  every generated file must have exactly one generated-file hash row; duplicate
  hash rows for the same generated file are rejected.
- Result:
  pass.

### Edge 5: Local Run Trace Could Become Open Command Authority

- Closeout containment:
  local run traces require argv-shaped command rows, command allowlist match,
  released sandbox policy, released run budget, and sandbox/network/secret/
  write-scope attestations.
- Result:
  pass.

### Edge 6: Command Row Ordering Could Mask Fixture Drift

- Closeout containment:
  command argv rows must be ordered by contiguous `arg_index` values with the
  executable first, and no runtime normalization is used to repair order.
- Result:
  pass.

### Edge 7: Sandbox Or Secret Violation Could Be Treated As Success

- Closeout containment:
  sandbox violation refs block `passed_local_probe` posture.
- Result:
  pass.

### Edge 8: Output Capture Could Become Unbounded Evidence Dump

- Closeout containment:
  stdout/stderr are represented by hashes plus bounded excerpts; filesystem
  side effects require pre/post manifests and diff refs.
- Result:
  pass.

### Edge 9: Probe Result Could Become Benchmark Truth

- Closeout containment:
  probe result logs require local-probe truth posture and hidden-test
  equivalence non-authority posture.
- Result:
  pass.

### Edge 10: Remand Could Use Hidden Or Forbidden Evidence

- Closeout containment:
  remand reason sources are closed to local probe failure, local sandbox
  violation, missing required artifact, unsupported behavior gap, or
  inconclusive trace; hidden-test, official evaluator, original-source, and
  decompilation sources remain forbidden.
- Result:
  pass.

### Edge 11: No-Correction Remand Could Require Invented Correction Rows

- Closeout containment:
  `remand_recorded_no_correction` records may carry empty correction attempts,
  while `corrected_for_local_reprobe` still requires correction attempts.
- Result:
  pass.

### Edge 12: Slice B Could Prematurely Emit C Artifacts

- Closeout containment:
  B emitted only candidate artifact manifest, local run trace, probe result
  log, and remand/correction record rows.
- Result:
  pass.

## Residual Edges

- `PB-RECON-0-C` must consume released `PB-RECON-0-A` and `PB-RECON-0-B`
  refs before auditing local equivalence or summarizing results.
- `PB-RECON-0-C` must keep `local_accepted` scoped only to the declared local
  probe set, not hidden tests, official evaluator results, benchmark truth, or
  model ranking.
- `PB-RECON-0-C` must block `local_accepted` posture on contamination,
  sandbox violations, missing required evidence, missing positive probe
  coverage, missing negative probe coverage, stdout/stderr mismatch,
  exit-code mismatch, or required filesystem side-effect mismatch.
- `PB-RECON-0-C` handoff pressure must not select official ProgramBench
  participation, benchmark-result governance, conceptual broker work, product,
  graph-memory, release, recursive-policy work, or a future family.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, broader conceptual
  broker implementation, V86/V87/V88 continuations, product, graph, release,
  or recursive-policy work remain unselected.

## Current Judgment

- `PB-RECON-0-B` is closed on `main` as a bounded local-evidence capture
  slice.
- `PB-RECON-0` remains open for `PB-RECON-0-C`; no family closeout has
  occurred.
- The shipped slice preserves the intended workbench membrane: it records
  local candidate artifacts, sandbox-bound run traces, local probe result
  logs, and cleanroom-local remand/correction rows, but it does not audit
  equivalence, claim local acceptance, run official ProgramBench, expose
  hidden tests, claim benchmark truth, score benchmarks, rank models, generate
  official submissions, transition runtime, or select a future family.
