# ADEU Studio Reasoning Benchmark Bundle Alignment

Authority layer: support / maintainer intake note only.

Source lane:

- imported external prototype bundle
- class: `X2`
- precedent status: `non_precedent`

## Artifact Relationship

- narrative ingress note:
  [CLAIMED_SCOPE.md](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/CLAIMED_SCOPE.md)
- unpacked source payload:
  [source_overlay](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/source_overlay)

This pack is an overlay-oriented import. Its payload preserves repo-relative code
surfaces exactly as claimed by the external bundle rather than being installed into the
live repo package paths.

## Claimed Scope

The imported narrative claims:

- doctrinal sharpening for the still-pending `V44` structural-reasoning lane
- operationalization for the still-pending `V46` benchmarking lane
- a new bounded proto-module at `packages/adeu_benchmarking`
- package-local schema export for benchmark and procedural-depth artifacts
- bootstrap wiring through `Makefile`
- targeted tests and replayable fixtures for `v46a` / `v46b`

## Observed Reachable Surfaces

The unpacked overlay actually contains:

- bootstrap wiring candidate at
  [source_overlay/Makefile](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/source_overlay/Makefile)
- package metadata at
  [source_overlay/packages/adeu_benchmarking/pyproject.toml](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/source_overlay/packages/adeu_benchmarking/pyproject.toml)
- package source under
  [source_overlay/packages/adeu_benchmarking/src/adeu_benchmarking](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/source_overlay/packages/adeu_benchmarking/src/adeu_benchmarking)
- package-local schema payload under
  [source_overlay/packages/adeu_benchmarking/schema](/home/rose/work/LexLattice/odeu/examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/source_overlay/packages/adeu_benchmarking/schema)

The imported payload does not contain:

- committed `packages/adeu_benchmarking/tests/...` content
- committed `packages/adeu_benchmarking/tests/fixtures/v46a/...`
- committed `packages/adeu_benchmarking/tests/fixtures/v46b/...`
- mirrored root `spec/benchmark_*.schema.json`
- mirrored root `spec/procedural_depth_*.schema.json`

## Accepted Shipped Scope

Current accepted shipped scope is intentionally narrow:

- intake pack only
- unpacked overlay only
- no live package addition
- no accepted schema contract
- no accepted benchmark artifact family release
- no accepted bootstrap/build integration

The five planning/spec docs from the same external bundle were aligned separately into
the live repo. That planning alignment does not promote this code payload into accepted
repo-owned package authority.

## Maintainer Alignment Notes

- The conceptual fit is strong. This is the best external code candidate so far for the
  still-pending `V44` / `V46` seam.
- The imported code is not merge-ready as delivered:
  - the narrative over-claims committed tests and root schema mirrors that are absent
    from the bundle
  - the package has at least one real materialization bug in
    `materialize_procedural_depth_instance_payload(...)`, where identity is computed
    before canonicalized `step_specs` ordering is validated
- The right interpretation is:
  - useful external shaping input
  - partial package skeleton
  - not yet repo-native implementation

## Required Before Internal Integration

- choose the concrete internal `V46` slice order rather than importing the package
  wholesale
- write an explicit prototype-to-repo mapping note for the benchmarking package
- re-author repo-owned tests and committed fixtures
- decide whether root `spec/` schema mirrors are required and, if so, wire them
  correctly
- fix canonical materialization / identity ordering for procedural-depth instances
- run repo-native verification under `.venv` and `make`, not only ad hoc smoke checks
