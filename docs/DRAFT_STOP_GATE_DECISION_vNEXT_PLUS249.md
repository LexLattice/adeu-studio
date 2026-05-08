# Draft Stop-Gate Decision vNext+249

Status: pre-start decision scaffold for `PB-RECON-0-B`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS249.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+249` / `PB-RECON-0-B` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS249.md`.
- It does not authorize official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, equivalence
  audit, result summary, handoff, family closeout alignment, unbounded command
  execution, target mutation outside the released sandbox, runtime transition,
  product authorization, graph-memory authority, recursive policy amendment,
  or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-RECON-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v78.md` |
| Prior slice closeout present | required | `PB-RECON-0-A` closed by `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md` |
| Slice-B lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS249.md` drafted |
| Slice scope is bounded | required | candidate artifact manifest, local run trace, probe result log, and remand/correction record only |
| Released work-order substrate required | required | B rows must consume released work order, worker context, exclusion manifest, sandbox policy, run budget, and guardrail refs |
| Local run trace is sandbox-bound | required | command allowlist, sandbox attestation, network/secret/write-scope attestations, and released budget refs required |
| Local output evidence is bounded | required | stdout/stderr hashes plus bounded excerpts; filesystem pre/post manifests and diff refs |
| Probe results stay local | required | no benchmark truth, hidden-test equivalence, official evaluator result, benchmark score, model ranking, or local accepted status |
| Remand source is cleanroom-local | required | hidden-test, official evaluator, original-source, and decompilation remands forbidden |
| Deferred C surfaces stay deferred | required | no equivalence audit, result summary, handoff, or family closeout rows |
| Official ProgramBench and benchmark truth stay absent | required | no official runner/evaluator, hidden tests, benchmark scores, model rankings, or official submissions |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=249` |

## Initial Stop-Gate Posture

- `PB-RECON-0-B` is the logical second slice after the released
  `PB-RECON-0-A` workbench boundary.
- The starter lock is coherent if it remains limited to local candidate
  artifact and local evidence capture under released sandbox/budget law.
- The implementation must wait until this `vNext+249` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_RECON_0B_STARTER_LOCK`
- rationale:
  - released `PB-RECON-0-A` now defines the work order, worker-visible
    context, auditor-only exclusions, sandbox policy, run budget, and
    non-authority guardrail;
  - `PB-RECON-0-B` can make local candidate artifacts and local run/probe
    evidence reviewable without claiming official ProgramBench status,
    hidden-test equivalence, benchmark truth, local accepted posture, or model
    ranking;
  - the slice must stay tightly bound to released A refs because it is the
    first execution-adjacent workbench surface.
