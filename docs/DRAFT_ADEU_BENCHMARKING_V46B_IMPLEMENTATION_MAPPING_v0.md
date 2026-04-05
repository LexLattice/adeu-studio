# Draft ADEU Benchmarking V46B Implementation Mapping v0

Status: support note for the `V46-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the imported GPT
Pro reasoning-benchmark prototype should be used as shaping evidence while the live
repo-owned `V46-B` implementation is re-authored in `packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS137.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46_IMPLEMENTATION_MAPPING_v0.md`
- `examples/external_prototypes/adeu-studio-reasoning-benchmark-bundle/ALIGNMENT.md`

## Carry Forward Nearly As-Is

- the `V46-A` substrate then `V46-B` concrete-projection split
- the tiny hierarchical `3x3` starter reference-chain idea
- the procedural-depth event vocabulary:
  - `activate`
  - `complete`
  - `return`
- structurally rich event objects rather than bare event-kind strings:
  - `event_index`
  - `step_ref`
  - `step_role`
  - optional parent/return targeting when relevant
- the three-way structural split reused at the concrete projection layer:
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  with `clean_success` and `mixed` preserved at the benchmark-diagnostic layer
- the starter boolean component-fidelity posture:
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
  with dominant-family derivation from that exact boolean pattern
- the starter artifact stack:
  - instance
  - gold trace
  - run trace
  - metrics
  - diagnostic report

## Re-Author With Repo Alignment

- re-author the concrete projection under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py`
- keep the live contract ids aligned to the ids already declared by the released
  `V46-A` projection spec:
  - `adeu_procedural_depth_instance@1`
  - `adeu_procedural_depth_gold_trace@1`
  - `adeu_procedural_depth_run_trace@1`
  - `adeu_procedural_depth_metrics@1`
  - `adeu_procedural_depth_diagnostic_report@1`
- consume the released family spec, projection spec, and execution context directly
  rather than cloning family/projection doctrine inside the procedural-depth module
- re-author repo-native deterministic fixtures and tests under:
  - `packages/adeu_benchmarking/tests/fixtures/v46b/`
  - `packages/adeu_benchmarking/tests/`
- require deterministic authoritative schema export plus root `spec/` mirrors
- keep component fidelity explicit instead of collapsing the slice into one-number
  benchmark scoring
- keep supporting event evidence trace-qualified across gold/run artifacts instead of
  using ambiguous unqualified event indexes
- fix the imported materialization/id-ordering bug:
  - canonicalize and validate `step_specs` before computing
    `procedural_depth_instance_id`
- keep hashing/canonicalization aligned with the shared repo helper inventory instead
  of reintroducing package-local drift

## Defer To Later Slice

- `V46-C` perturbation and non-regression widening
- `V46-D` additional benchmark projections and cross-subject comparison widening
- `V46-E` downstream consumer seams for routing/model/role/training research
- any API, web, or leaderboard surface over procedural-depth outputs
- any widening beyond the tiny hierarchical `3x3` starter family before `V46-B`
  itself is accepted

## Do Not Import

- the imported `procedural_depth.py` module wholesale into the live repo-owned package
- the imported instance-materialization path that computes ids before canonical step
  ordering is validated
- any assumption that the imported prototype’s schema names or fixture claims are
  already authoritative on `main`
- any widening from the tiny starter chain into larger benchmark families before later
  `V46` slices explicitly select it
- any silent promotion of the imported bundle from `non_precedent` shaping evidence to
  live package authority
