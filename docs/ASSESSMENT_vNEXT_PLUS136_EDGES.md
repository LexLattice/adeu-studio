# Assessment vNext+136 Edges

Status: post-closeout edge assessment for `V46-A` (April 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS136_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Benchmark Substrate Overclaims As Scoring Release

- Risk:
  the first benchmarking slice could act like a score, ranking, or leaderboard release
  instead of a bounded substrate release.
- Response:
  keep `V46-A` limited to family spec, projection spec, execution context, and
  validation report only, and forbid released procedural-depth scoring/reporting
  artifacts in the starter slice.
- Closeout Evidence:
  the shipped package/schema surface contains only the four starter benchmark
  contracts, and no procedural-depth instance, run-trace, metrics, or diagnostic
  artifact shipped in `v136`.

### Edge 2: Released `V44` Doctrine Is Quietly Rewritten

- Risk:
  `V46-A` could claim to be benchmarking while silently redefining the released
  structural split from `V44`.
- Response:
  let released `V44` constrain the benchmark dominant failure-family split and
  interpretation posture only, and forbid semantic redefinition of released `V44`
  probes, taxonomy, differential, suite, or recursive assessment law.
- Closeout Evidence:
  the released family/projection spec artifacts cite `V44` doctrine and schema ids as
  constraint sources only, and the live package does not ingest or reinterpret
  released `V44` payloads as runtime benchmark inputs.

### Edge 3: Projection Specs Smuggle In Unreleased Procedural-Depth Contracts

- Risk:
  declared downstream contract ids in the projection spec could be overread as if
  procedural-depth instance, trace, metrics, or diagnostic contracts already shipped.
- Response:
  make those fields declaration-only in `V46-A` and defer the actual released
  procedural-depth artifact families to `V46-B`.
- Closeout Evidence:
  the shipped projection spec declares the downstream `adeu_procedural_depth_*@1`
  contract ids while the package exports no such procedural-depth artifacts yet.

### Edge 4: Validation Report Pretends Fixture Cases Are Released Run Traces

- Risk:
  the starter validation report could overclaim replay evidence by treating local case
  refs as if they were already released benchmark run-trace artifacts.
- Response:
  keep `case_ref` fixture-scoped only in `V46-A` and forbid any claim that released
  run-trace contracts exist before `V46-B`.
- Closeout Evidence:
  the released validation report and helper keep `case_ref` fixture-scoped, and the
  package surface does not ship a run-trace schema family.

### Edge 5: Reliability Semantics Stay Hand-Wavy

- Risk:
  the substrate could name benchmark reliability without freezing whether the starter
  slice is expressing declared policy or empirical benchmark evidence.
- Response:
  require explicit reliability-policy and non-regression-policy summaries while making
  them declaration-only until later projection lanes release empirical benchmark
  artifacts.
- Closeout Evidence:
  the shipped family spec carries those summaries explicitly, and the closeout decision
  reiterates they remain policy-declarative only in `V46-A`.

### Edge 5A: Dominant-Family Field Blurs Success And Failure

- Risk:
  the starter dominant-family field could become semantically muddy because
  `clean_success` occupies the same field as actual failure families while `mixed`
  stays nominal only.
- Response:
  freeze `clean_success` as the only starter non-failure sentinel and require positive
  coverage for every released dominant-family value, including `mixed`.
- Closeout Evidence:
  the shipped `reference_v46a_validation_case_matrix.json` and validation-report
  fixture positively exercise all five released dominant-family values.

### Edge 6: Execution Context Drops The Snapshot Boundary

- Risk:
  benchmark artifacts could look comparable while lacking explicit repo snapshot or
  execution-context identity.
- Response:
  require explicit subject identity, determinism posture, fixed context-budget posture,
  and `repo_snapshot_ref` in every released execution-context artifact.
- Closeout Evidence:
  the released execution-context contract enforces those fields deterministically, and
  the committed reference fixture exercises them directly.

### Edge 6A: Starter Subject Taxonomy Overreads As Complete

- Risk:
  the narrower starter subject-under-test vocabulary could look like the full
  benchmarking-module taxonomy rather than a bounded first slice.
- Response:
  state explicitly that composite human-plus-tool-plus-model subject posture remains
  deferred from `V46-A`.
- Closeout Evidence:
  the released vocabulary remains bounded to the five starter classes only, and the
  closeout decision restates the composite subject posture as deferred.

### Edge 7: External Benchmark Bundle Becomes Silent Package Authority

- Risk:
  the normalized GPT Pro benchmark bundle could quietly determine the live `V46-A`
  contract set despite missing tests, missing root schema mirrors, and known
  materialization issues elsewhere in the bundle.
- Response:
  keep the external bundle support-only and re-author repo-owned `V46-A` surfaces,
  tests, fixtures, and schema exports under `packages/adeu_benchmarking`.
- Closeout Evidence:
  live implementation ownership remains entirely under `packages/adeu_benchmarking`,
  while the imported bundle stays normalized under `examples/external_prototypes/...`
  and non-precedent.

### Edge 8: Local Canonicalization And Schema Markers Drift From Repo Practice

- Risk:
  a new package-local hashing helper or raw `schema` field pattern could quietly drift
  from repo-wide canonical helper inventory and Pydantic alias practice, turning a
  narrow package slice into CI churn.
- Response:
  reuse shared canonical hashing helpers and the repo-standard alias-backed
  `schema_id <-alias-> schema` pattern rather than inventing new package-local
  exceptions.
- Closeout Evidence:
  review hardening in `1e994dfb7ba93bfcaba4f5107a2752de2e787c6b` replaced raw `schema`
  fields with alias-backed `schema_id` fields, reused `urm_runtime.hashing`, and
  restored the repo-wide canonical-helper inventory expected by the Python lane.

## Current Judgment

- `V46-A` was the right first slice because the benchmark family needed a released
  substrate and execution-context doctrine before releasing the first concrete
  procedural-depth benchmark projection.
- the shipped result remained properly bounded:
  - one repo-owned package
  - four released benchmark substrate schemas
  - deterministic authoritative schema export plus root mirrors
  - deterministic `v46a` fixtures and validation-report replay
  - explicit starter subject-under-test taxonomy
  - explicit benchmark-output epistemic posture
  - declaration-only downstream procedural-depth contract ids
  - explicit non-promotional interpretation posture
  - no procedural-depth instance/run/metrics/diagnostic release yet
- `V46-A` is now closed on `main` in the branch-local sense:
  - benchmark family spec
  - benchmark projection spec
  - benchmark execution context
  - benchmark validation report
- the next meaningful slice is `V46-B`:
  - the first concrete Procedural Depth Fidelity projection over the released
    benchmark substrate
  - not a reopening of substrate doctrine and not yet perturbation/non-regression or
    consumer widening
