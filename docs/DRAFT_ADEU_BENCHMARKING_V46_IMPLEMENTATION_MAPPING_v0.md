# Draft ADEU Benchmarking V46 Implementation Mapping v0

Status: support note for the pending `V46` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro reasoning-benchmark prototype should be used as shaping evidence while the live
repo-owned `V46` implementation is re-authored in `packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/DRAFT_BENCHMARKING_META_MODULE_SPEC_v0.md`
- `docs/DRAFT_PROCEDURAL_DEPTH_FIDELITY_BENCHMARK_SPEC_v0.md`
- `examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the family-level split between:
  - `V44` as doctrinal structure for what is being assessed
  - `V46` as benchmark substrate and measurement implementation
- the hierarchical structural-fidelity split:
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
- the generic benchmark substrate concepts:
  - benchmark family spec
  - benchmark projection spec
  - benchmark execution context
  - benchmark validation report
- the first concrete `V46-B` seed posture:
  - one tiny hierarchical `3x3` procedural-depth reference chain
  - one deterministic gold trace
  - one deterministic run-trace scorer
  - one dominant failure-family diagnostic result
- the starter procedural-depth event vocabulary:
  - `activate`
  - `complete`
  - `return`
- the three-way dominant failure-family posture:
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - with `clean_success` and `mixed` at the benchmark-diagnostic layer
- the bounded subject-under-test taxonomy from the imported substrate:
  - `base_model`
  - `prompted_model`
  - `routed_runtime`
  - `multi_agent_system`
  - `adeu_runtime_surface`

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/`
  - `packages/adeu_benchmarking/tests/`
- split the imported family cleanly across the pending internal slices:
  - `V46-A`:
    - benchmark family/projection substrate
    - execution-context contract
    - validation-report contract
  - `V46-B`:
    - procedural-depth instance
    - gold trace
    - run trace
    - metrics
    - diagnostic report
- re-author repo-native deterministic fixtures rather than trusting the imported
  narrative’s claimed `tests/fixtures/v46a` and `v46b` content
- re-author repo-native tests because the imported bundle does not actually include the
  claimed committed test files
- decide the authoritative schema naming set explicitly:
  - the imported narrative mentions generic `benchmark_metrics_report` and
    `benchmark_diagnostic_report`
  - the actual imported code currently provides:
    - `benchmark_validation_report`
    - `procedural_depth_metrics`
    - `procedural_depth_diagnostic_report`
- decide whether root `spec/` mirrors are required for this family and wire them
  intentionally if selected
- fix canonical materialization before any live adoption:
  - `materialize_procedural_depth_instance_payload(...)` currently computes identity
    before canonical `step_specs` ordering is validated
- bind schema export and package bootstrap to repo-native `.venv` / `make` verification
  rather than ad hoc `PYTHONPATH` smoke runs
- keep package-local hashing and canonicalization consistent with live repo practice and
  canonical-helper inventory

## Defer To Later Slice

- `V46-C` perturbation and non-regression widening
- `V46-D` additional benchmark projections and cross-subject comparison widening
- `V46-E` downstream consumer wiring for routing/model/role/training research
- any contest-world or `V43` consumer claim beyond the explicit planning relationship
- any leaderboard, promotion, or selection doctrine
- any widening from the tiny hierarchical reference chain into larger procedural-depth
  benchmark families before `V46-A` and `V46-B` are accepted

## Do Not Import

- the imported package tree wholesale into live `packages/adeu_benchmarking`
- the imported `Makefile` bootstrap edit before the package itself is repo-owned and
  tested
- the imported narrative as if it were authoritative evidence of committed tests,
  fixtures, or root `spec/` mirrors
- the claimed generic artifact names that are not actually backed by the imported code
  payload
- any silent promotion of the imported package from `non_precedent` external evidence to
  repo-native authority
- any raw full-snapshot overlay behavior from the earlier full-repo zip
