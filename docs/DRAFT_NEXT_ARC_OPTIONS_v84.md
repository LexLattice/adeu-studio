# Draft Next Arc Options v84

Status: planning handoff after `vNext+265` / `PB-CASE-EXPANSION-0-C`
merged on `main` and after the `PB-CASE-EXPANSION-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-CASE-EXPANSION-0` frontier. It does not
authorize local case execution, probe execution, batch command execution,
candidate materialization, matrix result projection, matrix summary,
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, baseline comparison, model ranking, leaderboard
standing, generated official submissions, official submission authority,
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
`DRAFT_NEXT_ARC_OPTIONS_v83.md`, which selected the
`PB-CASE-EXPANSION-0` ProgramBench local cleanroom case-expansion family.
`vNext+263`, `vNext+264`, and `vNext+265` then closed
`PB-CASE-EXPANSION-0-A`, `PB-CASE-EXPANSION-0-B`, and
`PB-CASE-EXPANSION-0-C` without creating additional family selector versions.

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
- `PB-CASE-EXPANSION-0` is closed on `main` as a local cleanroom case-supply
  governance family.
- latest closed implementation arc: `vNext+265`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v83.md`
- next planning obligation: select a post-`PB-CASE-EXPANSION-0` family
  without turning matrix inclusion pressure into execution, result
  projection, benchmark scoring, baseline comparison, model ranking, official
  ProgramBench participation, hidden-test inference, or batch execution.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

## Next Planning Question

Now that the repo can register new local cleanroom case lineages and emit
pressure-only matrix candidate handoffs, should the next practical family
govern how those ready lineages may be admitted into a local cleanroom matrix
revision without executing, scoring, ranking, or claiming benchmark coverage?

The candidate:

```text
PB-MATRIX-INCLUSION-0:
  ProgramBench Local Cleanroom Matrix Inclusion Governance
```

This selector treats `PB-MATRIX-INCLUSION-0` as a local matrix revision
governance family over already released local case lineages. It is not an
official ProgramBench runner, solver, evaluator integration, submission path,
hidden-test interface, benchmark score lane, baseline comparison lane,
leaderboard lane, model-ranking lane, batch execution lane, second-retry
lane, retry-chain lane, or official task-execution lane.

Controlling invariant:

```text
PB-MATRIX-INCLUSION-0 may make inclusion of ready local cleanroom case
lineages into a local matrix revision reviewable, but it may not run those
cases, project results, score the matrix, compare to baselines, rank models,
infer hidden-test behavior, contact official evaluators, or claim official
ProgramBench standing.
```

Matrix-inclusion invariant:

```text
Matrix inclusion is not execution and not result projection. A case admitted
to a local matrix revision becomes part of a declared local accounting set
only. Execution, local result projection, aggregate summaries, and any
baseline-relative interpretation remain future-family-only.
```

Case-supply invariant:

```text
Every included case must resolve to released cleanroom case lineage with clean
contamination posture, complete local probe/oracle coverage, source identity
hashes, non-representative benchmark posture, and pressure-only handoff basis.
```

## Recommended Next Pressure

- family / practical arc: `PB-MATRIX-INCLUSION-0`
- proposed name:
  - `PB-MATRIX-INCLUSION-0: ProgramBench Local Cleanroom Matrix Inclusion Governance`
- recommended planning posture:
  - select `PB-MATRIX-INCLUSION-0` as the next practical family after
    `PB-CASE-EXPANSION-0`;
  - select `PB-MATRIX-INCLUSION-0-A` as the next default candidate after this
    family bundle is reviewed;
  - consume released `PB-CASE-EXPANSION-0` lineage registrations, readiness
    summaries, and pressure-only matrix candidate handoffs as candidate
    supply;
  - consume released `PB-MATRIX-0` closeout and control doctrine as the
    baseline matrix-accounting substrate;
  - consume released `PB-TRIAL-0`, `PB-RETRY-0`, `PB-ATTEMPT-0`,
    `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` lineage as constraints, not
    new authority;
  - start with matrix inclusion request, candidate intake, eligibility review,
    control contract, and non-authority guardrail;
  - defer matrix amendment plan, case delta manifest, comparability delta
    review, contamination delta review, and inclusion decision records to
    `PB-MATRIX-INCLUSION-0-B`;
  - defer matrix revision registration, revision readiness summary,
    post-inclusion handoff, and family closeout alignment to
    `PB-MATRIX-INCLUSION-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-MATRIX-INCLUSION-0-A` | Matrix inclusion request, candidate intake, lineage eligibility review, control contract, and non-authority guardrail |
| `PB-MATRIX-INCLUSION-0-B` | Matrix amendment plan, case delta manifest, comparability delta review, contamination delta review, and inclusion decision record |
| `PB-MATRIX-INCLUSION-0-C` | Matrix revision registration, revision readiness summary, post-inclusion handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-MATRIX-INCLUSION-0-A` should be the first active slice. Candidate starter
surfaces:

- `programbench_local_matrix_inclusion_request@1`
- `programbench_local_matrix_candidate_intake@1`
- `programbench_local_matrix_inclusion_eligibility_review@1`
- `programbench_local_matrix_inclusion_control_contract@1`
- `programbench_local_matrix_inclusion_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom matrix-inclusion substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix_inclusion.py`;
- defer generic benchmark-suite, official-evaluator, leaderboard,
  batch-runner, baseline-comparison, or model-ranking splits to later
  families only if explicitly selected.

Avoid names such as `programbench_runner`, `programbench_eval`,
`programbench_solver`, `programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, `programbench_batch_runner`,
`programbench_baseline_scorer`, and `programbench_matrix_score`; those imply
official benchmark, solving, evaluation, submission, ranking, execution, or
score authority that this family does not select.

## `PB-MATRIX-INCLUSION-0-A` Output Contract

`PB-MATRIX-INCLUSION-0-A` should output only:

1. `programbench_local_matrix_inclusion_request@1`
2. `programbench_local_matrix_candidate_intake@1`
3. `programbench_local_matrix_inclusion_eligibility_review@1`
4. `programbench_local_matrix_inclusion_control_contract@1`
5. `programbench_local_matrix_inclusion_non_authority_guardrail@1`
6. deferred handoff notes for `PB-MATRIX-INCLUSION-0-B` and
   `PB-MATRIX-INCLUSION-0-C`

`PB-MATRIX-INCLUSION-0-A` must make the inclusion boundary stable enough to
answer:

```text
which released local case lineages are eligible candidates for a later local
matrix revision, under what controls, and with what non-authority posture?
```

It should not output:

- matrix amendment plan rows;
- matrix case delta manifest rows;
- inclusion decision rows;
- matrix revision registration rows;
- result projection rows;
- matrix summary rows;
- local trial dockets or executions;
- probe execution rows;
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

## Review-Hardened Requirements

The family review adds one core hardening: matrix inclusion must bind to a
specific base matrix and a specific proposed revision. A candidate inclusion
request should therefore carry:

- `base_matrix_ref`
- `base_matrix_revision_ref`
- `base_matrix_revision_hash`
- `target_matrix_revision_candidate_ref`
- `target_matrix_revision_candidate_hash`
- `prior_membership_manifest_hash`
- `proposed_membership_manifest_hash`
- `revision_delta_hash`

Validator:

```text
A candidate inclusion request is invalid unless it binds to exactly one
released base matrix revision and exactly one proposed revision candidate.
```

Candidate intake should keep each case row-shaped rather than flattening
lineage identity into a list. Each candidate row should carry lineage,
readiness, handoff, source-boundary, probe, oracle, contamination, and
dedupe fields. A case lineage already present in the base matrix cannot be
eligible for addition unless the request explicitly uses replacement/update
posture.

The A control contract should make non-representative and non-ranking posture
explicit:

```text
representativeness_posture = not_representative_benchmark_sample
inventory_count_posture = local_membership_accounting_only
benchmark_denominator_posture = not_benchmark_denominator
baseline_comparison_authority_posture = no_baseline_comparison_authority
```

For B, inclusion decisions must classify reasons as governance/accounting
reasons only. They must not use performance-selection reasons such as likely
pass/fail, expected score, model advantage, baseline improvement,
benchmark-representative status, or leaderboard relevance.

For C, revision readiness and post-inclusion handoff must remain
inventory-only and pressure-only. Counts are local membership inventory only,
not result counts or benchmark denominators.

## Non-Selected Alternatives

The following options remain unselected:

- `PB-BATCH-0`: batch execution over a local matrix;
- `PB-RESULT-0`: benchmark-like result or score governance;
- `PB-BASELINE-0`: baseline comparison governance;
- `PB-MODEL-COMPARE-0`: model comparison / ranking governance;
- official ProgramBench participation governance;
- official runner/evaluator integration;
- hidden evaluator result governance;
- generated official submission review;
- direct V86/V87/V88 continuation work.

## Recommendation

Select `PB-MATRIX-INCLUSION-0` as the next family for review. Do not implement
`PB-MATRIX-INCLUSION-0-A` until the family bundle and A/B/C implementation
mapping have been reviewed.
