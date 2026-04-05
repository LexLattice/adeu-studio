# Assessment vNext+136 Edges

Status: planning-edge assessment for `V46-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS136_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Benchmark Substrate Overclaims As Scoring Release

- Risk:
  the first benchmarking slice could act like a benchmark-score or leaderboard release
  instead of a bounded substrate release.
- Response:
  keep `V46-A` limited to family spec, projection spec, execution context, and
  validation report only, and forbid released metrics, diagnostic, ranking, and
  promotion surfaces in the starter slice.

### Edge 2: Released `V44` Doctrine Is Quietly Rewritten

- Risk:
  `V46-A` could claim to be benchmarking while silently redefining the released
  structural split from `V44`.
- Response:
  let released `V44` constrain the benchmark dominant failure-family split and
  interpretation posture only, and forbid semantic redefinition of released `V44`
  probes, taxonomy, differential, suite, or recursive assessment law.

### Edge 3: Projection Specs Smuggle In Unreleased Procedural-Depth Contracts

- Risk:
  declared downstream contract ids in the projection spec could be overread as if
  procedural-depth instance, trace, metrics, or diagnostic contracts already shipped.
- Response:
  make those fields declaration-only in `V46-A` and defer the actual released
  procedural-depth artifact families to `V46-B`.

### Edge 4: Validation Report Pretends Fixture Cases Are Released Run Traces

- Risk:
  the starter validation report could overclaim replay evidence by treating local case
  refs as if they were already released benchmark run-trace artifacts.
- Response:
  keep `case_ref` fixture-scoped only in `V46-A` and forbid any claim that released
  run-trace contracts exist before `V46-B`.

### Edge 5: Reliability Semantics Stay Hand-Wavy

- Risk:
  the substrate could name benchmark reliability without freezing the actual starter
  posture around determinism, repeated fixture replay, and benchmark limitations.
- Response:
  require explicit reliability-policy summaries in the family spec and deterministic
  validation scope plus benchmark limitations in the validation report, while keeping
  those reliability and non-regression summaries declaration-only until later
  projection lanes release empirical benchmark artifacts.

### Edge 5A: Dominant-Family Field Blurs Success And Failure

- Risk:
  the starter dominant-family field could become semantically muddy because
  `clean_success` occupies the same field as actual failure families.
- Response:
  freeze `clean_success` as the only starter non-failure sentinel inside the
  dominant-family field and require positive mixed-case coverage rather than leaving
  `mixed` nominal only.

### Edge 6: Execution Context Drops The Snapshot Boundary

- Risk:
  benchmark runs over repo-grounded artifacts could look comparable while lacking an
  explicit repo snapshot or execution-context identity.
- Response:
  require explicit subject identity, determinism posture, fixed context-budget posture,
  and `repo_snapshot_ref` in every released execution-context artifact.

### Edge 6A: Starter Subject Taxonomy Overreads As Complete

- Risk:
  the narrower starter subject-under-test vocabulary could look like the full
  benchmarking-module taxonomy rather than a bounded first slice.
- Response:
  state explicitly that composite human-plus-tool-plus-model subject posture remains
  deferred from `V46-A`.

### Edge 7: External Benchmark Bundle Becomes Silent Package Authority

- Risk:
  the normalized GPT Pro benchmark package could quietly determine the live `V46-A`
  contract set despite missing tests, missing root schema mirrors, and known
  materialization issues elsewhere in the bundle.
- Response:
  keep the external bundle support-only and re-author repo-owned `V46-A` surfaces,
  tests, fixtures, and schema exports under `packages/adeu_benchmarking`.

## Current Judgment

- `V46-A` is the right next move because `V44` is now fully released on `main`, so the
  benchmark family can consume the structural split as a constraint without forcing the
  first concrete procedural-depth projection too early.
- the starter slice should remain narrow and substrate-first:
  - one repo-owned package
  - four released benchmark substrate contracts only
  - explicit benchmark-output epistemic posture
  - explicit subject-under-test taxonomy
  - explicit deferral of composite human-plus-tool-plus-model subject posture
  - explicit execution-context capture
  - explicit deterministic validation posture
  - explicit policy-declarative reliability and non-regression summaries only
  - no released procedural-depth projection artifacts
  - no scoring, ranking, routing, or training-promotion doctrine
- if implementation stays that narrow, `V46-A` should set up a clean `V46-B`
  procedural-depth projection rather than collapsing the whole family into the imported
  prototype's partial package shape.
