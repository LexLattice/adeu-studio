# Draft ADEU Benchmarking V46C Implementation Mapping v0

Status: support note for the `V46-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
benchmarking prototype and the released `V46-A` / `V46-B` repo-owned surfaces should
shape a live `V46-C` perturbation/non-regression implementation in
`packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS138.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46B_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the `V46-A` substrate then `V46-B` baseline then `V46-C` perturbation ordering
- the requirement that released `V46-B` run traces, metrics, and diagnostics remain
  the authoritative baseline scorer surface
- operational perturbation cases rather than label-only expectation shells
- the perturbation-first, non-regression-second widening posture
- the need for bounded repeated-run replay before any cross-subject comparison claim
- the requirement that perturbation outputs remain diagnostic-only and
  non-promotional

## Re-Author With Repo Alignment

- re-author the live perturbation and non-regression lane under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py`
- keep the live contract ids aligned to the bounded `V46-C` starter set:
  - `adeu_procedural_depth_perturbation_case@1`
  - `adeu_procedural_depth_failure_topology@1`
  - `adeu_procedural_depth_non_regression_report@1`
  - `adeu_procedural_depth_benchmark_validation_report@1`
- consume the released `V46-B` instance/gold/run/metrics/diagnostic contracts
  directly rather than cloning baseline scorer doctrine
- freeze starter evaluation to `deterministic_fixed_context` only
- freeze exact-match non-regression thresholds over:
  - run-trace id
  - metrics id
  - diagnostic-report id
  - dominant failure family
  - terminal trace status
- re-author aggregation artifacts with explicit per-case and per-replay structure
  rather than ambiguous parallel arrays
- re-author repo-native deterministic fixtures and tests under:
  - `packages/adeu_benchmarking/tests/fixtures/v46c/`
  - `packages/adeu_benchmarking/tests/`
- require deterministic authoritative schema export plus root `spec/` mirrors
- keep perturbation evidence and non-regression summaries bundle-scoped instead of
  letting them drift into projection-library or cross-subject claims

## Defer To Later Slice

- `V46-D` additional benchmark projections and cross-subject comparison widening
- `V46-E` downstream consumer seams for routing/model/role/training research
- any API, web, leaderboard, or ranking surface over perturbation outputs
- any stochastic tolerance or broad variance-floor doctrine beyond the frozen starter
  replay count

## Do Not Import

- any second scorer family that forks the released `V46-B` baseline contracts
- any direct jump from perturbation evidence to routing/model/training authority
- any silent promotion of tiny-bundle replay stability into broad empirical benchmark
  reliability
- any cross-subject or benchmark-library widening before `V46-D`
