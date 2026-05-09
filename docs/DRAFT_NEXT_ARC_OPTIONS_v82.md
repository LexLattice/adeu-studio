# Draft Next Arc Options v82

Status: planning handoff after `vNext+259` / `PB-RETRY-0-C` merged on
`main` and after the `PB-RETRY-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-RETRY-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, leaderboard standing, generated official submissions, official
submission authority, second retry authority, retry-chain authority,
unbounded command execution, target mutation outside a released local
sandbox/write scope, runtime transition, product authorization, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release,
or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v81.md`, which selected the `PB-RETRY-0`
ProgramBench local cleanroom retry-governance family. `vNext+257`,
`vNext+258`, and `vNext+259` then closed `PB-RETRY-0-A`,
`PB-RETRY-0-B`, and `PB-RETRY-0-C` without creating additional family
selector versions.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `PB-PY-0` is closed on `main` as a local ProgramBench-shaped Python
  reconstruction realization research family.
- `PB-ADAPTER-0` is closed on `main` as a ProgramBench cleanroom adapter
  membrane family.
- `PB-RECON-0` is closed on `main` as a local cleanroom reconstruction
  workbench family.
- `PB-ATTEMPT-0` is closed on `main` as a local cleanroom reconstruction
  attempt lifecycle family.
- `PB-TRIAL-0` is closed on `main` as a single local cleanroom reconstruction
  trial family.
- `PB-RETRY-0` is closed on `main` as a single local cleanroom retry
  governance family.
- latest closed implementation arc: `vNext+259`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v81.md`
- next planning obligation: select a post-`PB-RETRY-0` family without turning
  local retry settlement, same-lineage delta observations, local acceptance,
  local remand settlement, or case-level aggregation into benchmark truth,
  model ranking, official ProgramBench participation, second retry authority,
  retry-chain authority, or official submission authority.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that the repo can govern one local cleanroom trial and one bounded local
retry, should the next practical family govern a local cleanroom case matrix:
a small set of released case lineages that can be included, projected,
observed, and summarized under common cleanroom controls without becoming an
official benchmark run or model-ranking surface?

The candidate:

```text
PB-MATRIX-0:
  ProgramBench Local Cleanroom Case Matrix Governance
```

This selector treats `PB-MATRIX-0` as a local case-matrix family over released
`PB-TRIAL-0` and `PB-RETRY-0` lineages. It is not an official ProgramBench
runner, solver, evaluator integration, submission path, hidden-test
interface, benchmark score lane, leaderboard lane, model-ranking lane,
second-retry lane, retry-chain lane, or official task-execution lane.

Controlling invariant:

```text
PB-MATRIX-0 may make a local cleanroom case matrix reviewable, but it may not
turn case inclusion, per-case result projection, aggregate observation, local
acceptance counts, remand counts, or matrix summaries into benchmark truth,
official ProgramBench standing, hidden-test equivalence, model ranking,
second retry authority, retry-chain authority, official submission authority,
or future-family selection.
```

Operational matrix invariant:

```text
Case aggregation is not benchmark scoring. A matrix row may preserve local
case posture, coverage, blockers, and lineage, but it may not rank models,
claim leaderboard standing, infer hidden-test success, or launder official
evaluator feedback into local cleanroom evidence.
```

Case-lineage invariant:

```text
Every matrix case must resolve to released local cleanroom case lineage:
PB-ADAPTER case packet law, PB-RECON workbench law, PB-ATTEMPT lifecycle law,
PB-TRIAL specimen law, and optional PB-RETRY settlement law. Unreleased,
contaminated, hidden-test-derived, official-evaluator-derived, or
source-lookup-derived cases are not matrix-ready.
```

## Recommended Next Pressure

- family / practical arc: `PB-MATRIX-0`
- proposed name:
  - `PB-MATRIX-0: ProgramBench Local Cleanroom Case Matrix Governance`
- recommended planning posture:
  - select `PB-MATRIX-0` as the next practical family after `PB-RETRY-0`;
  - select `PB-MATRIX-0-A` as the next default candidate for `vNext+260`
    after this family bundle is reviewed;
  - consume released `PB-RETRY-0` outcome audit, delta observation summary,
    remand settlement, family closeout alignment, and released retry A/B
    lineage as optional retry-settlement substrate;
  - consume released `PB-TRIAL-0`, `PB-ATTEMPT-0`, `PB-RECON-0`,
    `PB-ADAPTER-0`, and `PB-PY-0` closeout lineage as constraints, not new
    authority;
  - start with matrix request, case inclusion manifest, case lineage
    eligibility review, matrix control contract, and matrix non-authority
    guardrail;
  - defer per-case result projection, matrix observation ledger, coverage
    register, and contamination register to `PB-MATRIX-0-B`;
  - defer matrix summary, matrix handoff, and family closeout alignment to
    `PB-MATRIX-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-MATRIX-0-A` | Matrix request, case inclusion manifest, case lineage eligibility review, matrix control contract, and non-authority guardrail |
| `PB-MATRIX-0-B` | Per-case result projection, local matrix observation ledger, matrix coverage register, and contamination register |
| `PB-MATRIX-0-C` | Local matrix summary, post-matrix handoff pressure, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-MATRIX-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_local_case_matrix_request@1`
- `programbench_local_case_inclusion_manifest@1`
- `programbench_local_case_lineage_eligibility_review@1`
- `programbench_local_case_matrix_control_contract@1`
- `programbench_local_case_matrix_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom case-matrix substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py`;
- defer any generic benchmark-suite, leaderboard, or model-ranking split to a
  later family only if explicitly selected.

Avoid names such as `programbench_runner`, `programbench_eval`,
`programbench_solver`, `programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, and `programbench_batch_runner`; those imply
official benchmark, solving, evaluation, submission, ranking, or execution
authority that this family does not select.

## `PB-MATRIX-0-A` Output Contract

`PB-MATRIX-0-A` should output only:

1. `programbench_local_case_matrix_request@1`
2. `programbench_local_case_inclusion_manifest@1`
3. `programbench_local_case_lineage_eligibility_review@1`
4. `programbench_local_case_matrix_control_contract@1`
5. `programbench_local_case_matrix_non_authority_guardrail@1`
6. deferred handoff notes for `PB-MATRIX-0-B` and `PB-MATRIX-0-C`

`PB-MATRIX-0-A` must make the matrix boundary stable enough to answer:

```text
which released local cleanroom case lineages are eligible to enter a local
case matrix, under what shared controls, and with what non-authority posture?
```

It should not output:

- per-case result projection rows;
- matrix observation ledger rows;
- matrix coverage register rows;
- matrix contamination register rows;
- matrix summary rows;
- benchmark scores;
- model rankings;
- leaderboard or comparative model claims;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- generated official submissions;
- second retry or retry-chain authority;
- command execution;
- candidate materialization;
- future-family selection.

`PB-MATRIX-0-A` may consume released `PB-TRIAL-0` and `PB-RETRY-0` rows only
as local case-lineage substrate. Those rows must not be treated as benchmark
truth, official ProgramBench outcome, model-comparison evidence, or authority
to widen the worker-visible context. Matrix summary and aggregate observation
can appear only after later `PB-MATRIX-0-B` projection rows and
`PB-MATRIX-0-C` summary rows exist.

The A starter should make these readiness facts explicit:

- `case_matrix_ref`
- `matrix_request_ref`
- `matrix_horizon`
- `matrix_max_case_count`
- `case_inclusion_manifest_ref`
- `case_lineage_eligibility_review_ref`
- `matrix_control_contract_ref`
- `matrix_case_candidate_refs`
- `matrix_case_candidate_rows`
- `matrix_selection_rationale_rows`
- `released_case_lineage_refs`
- `case_lineage_kind`
- `case_origin_posture`
- `case_visibility_posture`
- `case_contamination_posture`
- `case_result_source_posture`
- `case_retry_settlement_posture`
- `matrix_worker_profile_control_ref`
- `matrix_tool_policy_control_ref`
- `matrix_probe_basis_control_ref`
- `multi_profile_matrix_posture`
- `aggregate_count_posture`
- `representativeness_posture`
- `matrix_non_ranking_posture`
- `official_benchmark_authority_posture`

`PB-MATRIX-0-A` should reject a matrix case if it is unreleased,
contaminated, hidden-test-derived, official-evaluator-derived,
source-lookup-derived, postmortem-only, missing required local lineage, or
claiming benchmark truth / model ranking. It should also reject:

- a matrix request that claims representative benchmark coverage for a local
  smoke / research / coverage-probe matrix;
- a matrix request that uses multiple worker/model profiles without
  `multi_profile_matrix_posture =
  comparability_accounting_only_no_ranking`;
- soft scoring language such as pass rate, solve rate, success rate,
  model wins, beats baseline, leaderboard-like, representative benchmark
  subset, or official-like score.

## Non-Selected Arcs

This selector maps but does not select:

- official ProgramBench participation;
- official runner/evaluator integration;
- hidden evaluator result governance;
- benchmark-result or benchmark-score governance;
- model-ranking or leaderboard surfaces;
- second retry or retry-chain governance;
- batch command execution over case matrices;
- generated official submission review;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- generalized multi-language realization overlays;
- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack review;
- `V88` deterministic closeout transition / remand routing;
- canonical implementation-lock review;
- product authority, graph-memory authority, release authority, or recursive
  policy amendment.

## Decision

Recommended selection:

```text
select PB-MATRIX-0 as the next ProgramBench practical family
select PB-MATRIX-0-A as the next slice candidate after review
do not select official ProgramBench participation, benchmark scoring,
model ranking, hidden-test handling, second retry authority, or batch
execution
```

Post-`PB-MATRIX-0-A` continuation posture: after `vNext+260` closes on
`main`, select `PB-MATRIX-0-B` as the next default candidate inside the
already selected `PB-MATRIX-0` family, subject to its own `vNext+261` lock,
stop-gate decision, and edge assessment.

Post-`PB-MATRIX-0-B` continuation posture: after `vNext+261` closes on
`main`, select `PB-MATRIX-0-C` as the next default candidate inside the
already selected `PB-MATRIX-0` family, subject to its own `vNext+262` lock,
stop-gate decision, and edge assessment.
