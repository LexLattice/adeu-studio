# Draft ADEU Benchmarking V46A Implementation Mapping v0

Status: support note for the `V46-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro reasoning-benchmark prototype should be used as shaping evidence while the live
repo-owned `V46-A` implementation is re-authored in `packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS136.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the bounded package-first move into:
  - `packages/adeu_benchmarking`
- the generic starter substrate split between:
  - benchmark family spec
  - benchmark projection spec
  - benchmark execution context
  - benchmark validation report
- the bounded subject-under-test taxonomy:
  - `base_model`
  - `prompted_model`
  - `routed_runtime`
  - `multi_agent_system`
  - `adeu_runtime_surface`
- the starter narrowing that keeps composite human-plus-tool-plus-model subject posture
  deferred from `V46-A`
- the bounded dominant benchmark failure-family vocabulary:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
  with `clean_success` treated as a non-failure sentinel inside that starter field
- deterministic validation-case replay as the first benchmark-self-validation posture

## Re-Author With Repo Alignment

- create the repo-owned package scaffold under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/`
  - `packages/adeu_benchmarking/tests/`
- re-author the starter substrate in `models.py` rather than copying the prototype
  `family.py` wholesale
- use repo-owned schema ids with the `adeu_` prefix:
  - `adeu_benchmark_family_spec@1`
  - `adeu_benchmark_projection_spec@1`
  - `adeu_benchmark_execution_context@1`
  - `adeu_benchmark_validation_report@1`
- keep the released `V44` family as a constraint source only:
  - it informs dominant benchmark failure-family posture
  - it does not become a required live runtime artifact input in `V46-A`
- enrich the starter family spec so reliability and non-regression posture are explicit
  instead of implicit, while keeping those summaries policy-declarative only in
  `V46-A`
- enrich the starter execution context with:
  - `context_budget_posture`
  - optional `orchestration_topology_ref`
- change imported validation-case payloads from `run_trace_ref` to fixture-scoped
  `case_ref` in `V46-A`, because released run-trace contracts are deferred to `V46-B`
- require deterministic authoritative schema exports plus root `spec/` mirrors
- add repo-native deterministic fixtures and targeted tests
- include positive starter validation coverage for:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- wire bootstrap/install support intentionally through repo-native `Makefile` updates if
  the new package needs them for `make check`

## Defer To Later Slice

- `V46-B`:
  - `adeu_procedural_depth_instance@1`
  - `adeu_procedural_depth_gold_trace@1`
  - `adeu_procedural_depth_run_trace@1`
  - `adeu_procedural_depth_metrics@1`
  - `adeu_procedural_depth_diagnostic_report@1`
- any live scorer over released procedural-depth run traces
- any repeated-run perturbation or non-regression widening to `V46-C`
- any cross-subject comparison widening to `V46-D`
- any routing/model/role/training consumer seam to `V46-E`

## Do Not Import

- the imported `procedural_depth.py` module into live `V46-A` package paths
- imported procedural-depth artifact names as if they are already released in `V46-A`
- the imported `run_trace_ref`-based validation case shape unchanged into the starter
  repo-owned validation report
- the imported narrative claim that tests and root `spec/` mirrors already exist
- the imported `Makefile` edit before the repo-owned package and tests actually land
- any raw overlay behavior that treats the external bundle as precedent-bearing live
  authority
