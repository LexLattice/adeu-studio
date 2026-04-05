# Draft Stop-Gate Decision vNext+136

Status: proposed gate for `V46-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS136.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- `packages/adeu_benchmarking` remains the only active `V46-A` package;
- four starter benchmark contracts export and mirror deterministically:
  - `adeu_benchmark_family_spec@1`
  - `adeu_benchmark_projection_spec@1`
  - `adeu_benchmark_execution_context@1`
  - `adeu_benchmark_validation_report@1`;
- released `V44` remains a constraining doctrinal source only, with no semantic
  redefinition of released `V44` surfaces inside `V46-A`;
- projection specs declare downstream procedural-depth contract ids explicitly without
  treating them as already released artifacts in the starter slice;
- starter reliability and non-regression summaries remain policy-declarative only and
  do not overclaim empirical confirmation before later projection lanes;
- execution contexts require explicit subject identity, determinism posture,
  repo-snapshot identity, and fixed context-budget posture;
- validation reports remain deterministic and fixture-scoped, with no requirement for a
  released benchmark run-trace contract yet;
- positive validation-case coverage exists for at least:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`;
- `clean_success` remains explicit as the only starter non-failure sentinel inside the
  dominant-family field;
- composite human-plus-tool-plus-model subject-under-test posture remains explicitly
  deferred from the starter vocabulary;
- reject fixtures fail closed for:
  - missing declared downstream contract ids on projection specs;
  - unsupported dominant failure-family vocabulary in validation reports;
- no released procedural-depth instance, gold-trace, run-trace, metrics, or
  diagnostic-report contracts appear in the `V46-A` package surface;
- targeted tests cover deterministic ids, canonical ordering, schema export replay,
  validation-report derivation, and fixture-scoped reject posture.

## Do Not Accept If

- the slice silently promotes the imported GPT Pro benchmark bundle into live package
  authority;
- `V46-A` claims benchmark scoring, rankings, leaderboards, routing authority, or
  training entitlement;
- validation `case_ref` values masquerade as released run-trace contracts before
  `V46-B`;
- released `V44` structural doctrine is rewritten rather than constrained by the
  starter benchmark substrate;
- root `spec/` mirrors are claimed in docs but missing from the released package lane;
- the starter slice ships procedural-depth-specific artifact families that belong to
  `V46-B`.

## Local Gate

- run `make arc-start-check ARC=136`
