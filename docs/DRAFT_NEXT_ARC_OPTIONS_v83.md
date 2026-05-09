# Draft Next Arc Options v83

Status: planning handoff after `vNext+262` / `PB-MATRIX-0-C` merged on
`main` and after the `PB-MATRIX-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-MATRIX-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, model ranking, leaderboard standing, generated
official submissions, official submission authority, batch command execution,
second retry authority, retry-chain authority, unbounded command execution,
target mutation outside a released local sandbox/write scope, runtime
transition, product authorization, graph-memory authority, recursive policy
amendment, PR creation, commit, merge, release, or future-family selection by
itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v82.md`, which selected the `PB-MATRIX-0`
ProgramBench local cleanroom case-matrix family. `vNext+260`,
`vNext+261`, and `vNext+262` then closed `PB-MATRIX-0-A`,
`PB-MATRIX-0-B`, and `PB-MATRIX-0-C` without creating additional family
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
- `PB-MATRIX-0` is closed on `main` as a local cleanroom case-matrix
  accounting family.
- latest closed implementation arc: `vNext+262`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v82.md`
- next planning obligation: select a post-`PB-MATRIX-0` family without
  turning local case expansion, new local case lineage, local probe contracts,
  or future matrix inclusion pressure into official ProgramBench participation,
  batch execution, benchmark score, baseline-relative result, model ranking,
  hidden-test inference, or official submission authority.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

## Next Planning Question

Now that the repo can account for released local case lineages in a matrix,
should the next practical family govern how to add a small number of new local
cleanroom case lineages so later arcs can run a few actual local trials under
existing law?

The candidate:

```text
PB-CASE-EXPANSION-0:
  ProgramBench Local Cleanroom Case Expansion Governance
```

This selector treats `PB-CASE-EXPANSION-0` as local cleanroom case expansion
over released ProgramBench substrate. It is not an official ProgramBench
runner, solver, evaluator integration, submission path, hidden-test
interface, benchmark score lane, leaderboard lane, model-ranking lane, batch
execution lane, second-retry lane, retry-chain lane, or official
task-execution lane.

Controlling invariant:

```text
PB-CASE-EXPANSION-0 may make new local cleanroom case lineages reviewable,
but it may not run those cases, score them, compare them to baselines, rank
models, infer hidden-test behavior, contact official evaluators, or claim
official ProgramBench standing.
```

Case-expansion invariant:

```text
Case expansion is not batch execution. A newly registered local case may
carry cleanroom evidence, expected local probes, source boundaries, oracle
boundaries, contamination checks, and matrix-inclusion pressure, but it may
not become an executed trial, official task result, benchmark score, or
baseline-relative result without a later selected family.
```

Source-boundary invariant:

```text
Every expanded local case must preserve cleanroom source lineage. Hidden
tests, official evaluator feedback, original source, decompilation facts,
internet/source lookup, external repo facts, host secrets, Docker socket
material, and postmortem-only evidence remain excluded, including through
derived summaries.
```

## Recommended Next Pressure

- family / practical arc: `PB-CASE-EXPANSION-0`
- proposed name:
  - `PB-CASE-EXPANSION-0: ProgramBench Local Cleanroom Case Expansion Governance`
- recommended planning posture:
  - select `PB-CASE-EXPANSION-0` as the next practical family after
    `PB-MATRIX-0`;
  - select `PB-CASE-EXPANSION-0-A` as the next default candidate for
    `vNext+263` after this family bundle is reviewed;
  - consume released `PB-MATRIX-0` family closeout as the local matrix
    accounting substrate;
  - consume released `PB-TRIAL-0`, `PB-RETRY-0`, `PB-ATTEMPT-0`,
    `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` lineage as constraints, not
    new authority;
  - start with case-expansion request, source pool manifest, eligibility
    review, control contract, and non-authority guardrail;
  - defer case blueprints, cleanroom evidence packs, probe contracts, oracle
    boundaries, and contamination screens to `PB-CASE-EXPANSION-0-B`;
  - defer case lineage registration, readiness summary, matrix candidate
    handoff, and family closeout alignment to `PB-CASE-EXPANSION-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-CASE-EXPANSION-0-A` | Expansion request, source pool manifest, expansion eligibility review, expansion control contract, and non-authority guardrail |
| `PB-CASE-EXPANSION-0-B` | Local case blueprint, cleanroom evidence pack, probe contract, oracle boundary, and contamination screen |
| `PB-CASE-EXPANSION-0-C` | Local case lineage registration, expansion readiness summary, matrix candidate handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-CASE-EXPANSION-0-A` should be the first active slice. Candidate starter
surfaces:

- `programbench_local_case_expansion_request@1`
- `programbench_local_case_source_pool_manifest@1`
- `programbench_local_case_expansion_eligibility_review@1`
- `programbench_local_case_expansion_control_contract@1`
- `programbench_local_case_expansion_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom case-expansion substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_case_expansion.py`;
- defer generic benchmark-suite, official-evaluator, leaderboard,
  batch-runner, or model-ranking splits to later families only if explicitly
  selected.

Avoid names such as `programbench_runner`, `programbench_eval`,
`programbench_solver`, `programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, `programbench_batch_runner`, and
`programbench_baseline_scorer`; those imply official benchmark, solving,
evaluation, submission, ranking, execution, or score authority that this
family does not select.

## `PB-CASE-EXPANSION-0-A` Output Contract

`PB-CASE-EXPANSION-0-A` should output only:

1. `programbench_local_case_expansion_request@1`
2. `programbench_local_case_source_pool_manifest@1`
3. `programbench_local_case_expansion_eligibility_review@1`
4. `programbench_local_case_expansion_control_contract@1`
5. `programbench_local_case_expansion_non_authority_guardrail@1`
6. deferred handoff notes for `PB-CASE-EXPANSION-0-B` and
   `PB-CASE-EXPANSION-0-C`

`PB-CASE-EXPANSION-0-A` must make the expansion boundary stable enough to
answer:

```text
which cleanroom-visible source pools and candidate case ideas are eligible
for later local case blueprinting, under what controls, and with what
non-authority posture?
```

It should not output:

- local case blueprint rows;
- cleanroom evidence pack rows;
- probe contract rows;
- oracle boundary rows;
- contamination screen rows;
- case lineage registration rows;
- matrix inclusion rows;
- local trial dockets or executions;
- candidate implementation artifacts;
- batch execution rows;
- benchmark scores;
- baseline-relative result rows;
- model rankings;
- leaderboard or comparative model claims;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- generated official submissions;
- second retry or retry-chain authority;
- command execution;
- future-family selection.

The A starter should make these readiness facts explicit:

- `case_expansion_ref`
- `case_expansion_request_ref`
- `expansion_horizon`
- `expansion_max_case_count`
- `source_pool_manifest_ref`
- `expansion_eligibility_review_ref`
- `expansion_control_contract_ref`
- `candidate_case_idea_refs`
- `candidate_case_idea_rows`
- `case_selection_horizon`
- `case_selection_rationale_rows`
- `case_selection_bias_posture`
- `case_diversity_posture`
- `dedupe_policy_ref`
- `source_pool_rows`
- `allowed_source_refs`
- `forbidden_source_refs`
- `source_visibility_posture`
- `source_origin_posture`
- `derived_summary_policy`
- `case_origin_posture`
- `candidate_case_idea_hash`
- `source_pool_subset_hash`
- `dedupe_against_existing_case_lineages`
- `existing_case_lineage_overlap_refs`
- `nearest_existing_case_refs`
- `novelty_or_duplication_posture`
- `case_blueprint_deferred_posture`
- `local_execution_deferred_posture`
- `matrix_inclusion_deferred_posture`
- `representativeness_posture`
- `official_benchmark_authority_posture`
- `benchmark_score_authority_posture`
- `model_ranking_posture`

`PB-CASE-EXPANSION-0-A` should reject a source pool or candidate case idea if
it is hidden-test-derived, official-evaluator-derived,
original-source-derived, decompilation-derived, internet-derived,
external-repo-derived, postmortem-only, missing source identity, missing
visibility posture, support-only, contaminated, or claiming benchmark truth /
baseline-relative score / model ranking. It should also reject:

- hidden or forbidden source names, paths, excerpts, test names, semantic
  summaries, or derived facts in worker-visible or blueprint-visible advisory
  rows;
- a request that authorizes local execution, batch execution, official
  evaluator access, or baseline scoring;
- case ideas that rely on globs instead of concrete source refs;
- a candidate case idea marked eligible while duplicating an existing
  released local case lineage without explicit smoke/regression rationale;
- expansion controls that widen visibility beyond released cleanroom law.

Named source-law validator:

```text
no_derived_summary_laundering:
  forbidden, hidden, postmortem-only, source-derived, evaluator-derived, or
  auditor-only sources may not be transformed into visible advisory facts,
  labels, case ideas, behavior obligations, probe expectations, or oracle
  boundary claims.
```

## Non-Selected Arcs

This selector maps but does not select:

- batch execution governance;
- benchmark-result or benchmark-score governance;
- baseline-relative scoring or baseline comparison governance;
- official ProgramBench participation;
- official runner/evaluator integration;
- hidden evaluator result governance;
- model-ranking or leaderboard surfaces;
- second retry or retry-chain governance;
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
select PB-CASE-EXPANSION-0 as the next ProgramBench practical family
select `PB-CASE-EXPANSION-0-A` as the next default candidate after review
do not select batch execution, benchmark scoring, baseline comparison,
official ProgramBench participation, model ranking, hidden-test handling, or
future-family selection
```

Post-`PB-CASE-EXPANSION-0-A` continuation posture: after `vNext+263` closes
on `main`, select `PB-CASE-EXPANSION-0-B` as the next default candidate
inside the already selected `PB-CASE-EXPANSION-0` family, subject to its own
`vNext+264` lock, stop-gate decision, and edge assessment.

Post-`PB-CASE-EXPANSION-0-B` continuation posture: after `vNext+264` closes
on `main`, select `PB-CASE-EXPANSION-0-C` as the next default candidate
inside the already selected `PB-CASE-EXPANSION-0` family, subject to its own
`vNext+265` lock, stop-gate decision, and edge assessment.
