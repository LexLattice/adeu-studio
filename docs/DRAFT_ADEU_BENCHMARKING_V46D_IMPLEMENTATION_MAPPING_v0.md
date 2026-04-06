# Draft ADEU Benchmarking V46D Implementation Mapping v0

Status: support note for the `V46-D` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the broader
benchmarking family and the released `V46-A`, `V46-B`, and `V46-C` repo-owned surfaces
should shape a live `V46-D` cross-subject comparison implementation in
`packages/adeu_benchmarking`.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS139.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_BENCHMARKING_V46C_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- the `V46-A` substrate then `V46-B` baseline then `V46-C` perturbation ordering
- the requirement that released `V46-B` and `V46-C` artifacts remain the authoritative
  comparison inputs
- the diagnostic-first and non-promotional output posture
- the need for deterministic context before any cross-subject widening claim
- the requirement that comparison reports keep per-subject evidence explicit rather
  than collapsing into one-number promotion

## Re-Author With Repo Alignment

- re-author the live comparison lane under:
  - `packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py`
- keep the live contract ids aligned to the bounded `V46-D` starter set:
  - `adeu_benchmark_subject_record@1`
  - `adeu_cross_subject_comparison_case@1`
  - `adeu_cross_subject_comparison_report@1`
  - `adeu_cross_subject_comparison_validation_report@1`
- consume released `V46-A` family/projection/execution-context refs directly
- consume released `V46-B` baseline run/metrics/diagnostic refs directly
- consume released `V46-C` non-regression and validation refs directly
- freeze starter subject classes to:
  - `base_model`
  - `prompted_model`
- re-author subject-specific execution-context handling so the starter pair uses
  distinct execution-context refs with one frozen compatibility law over:
  - `repo_snapshot_ref`
  - `tool_availability`
  - `context_budget_posture`
  - `determinism_posture`
- freeze starter comparison to one deterministic subject pair over one released
  Procedural Depth bundle only
- carry one explicit perturbation-bundle anchor plus ordered perturbation-case refs so
  cross-subject sameness is not inferred only indirectly from aggregate reports
- freeze the per-surface comparison mapping over released fields only:
  - baseline structural fidelity
  - perturbation non-regression
  - perturbation validation
- re-author repo-native deterministic fixtures and tests under:
  - `packages/adeu_benchmarking/tests/fixtures/v46d/`
  - `packages/adeu_benchmarking/tests/`
- require deterministic authoritative schema export plus root `spec/` mirrors

## Defer To Later Slice

- broader benchmark-projection-library widening inside `V46-D`
- richer subject-class coverage beyond the starter pair
- leaderboard, ranking, or promotional comparison surfaces
- `V46-E` downstream consumer seams for routing/model/role/training research
- any API or web surface over benchmark comparisons

## Do Not Import

- any second scorer family that forks released `V46-B` or `V46-C` law
- any comparison artifact that promotes a subject as a winner or routing authority
- any immediate widening into multiple new benchmark projections
- any stochastic or confidence-floor doctrine in the starter comparison lane
