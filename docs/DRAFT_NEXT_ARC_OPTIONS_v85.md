# Draft Next Arc Options v85

Status: planning handoff after `vNext+268` / `PB-MATRIX-INCLUSION-0-C`
merged on `main` and after the `PB-MATRIX-INCLUSION-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-MATRIX-INCLUSION-0` frontier. It does not
authorize official ProgramBench participation, official task execution,
official runner integration, official evaluator integration, hidden-test
handling, hidden-test inference, hidden-test equivalence, original source
lookup, decompilation, internet lookup inside ProgramBench tasks, external
repository lookup, benchmark submission, benchmark scoring, benchmark truth,
pass rate, solve rate, success rate, baseline comparison, model ranking,
leaderboard standing, generated official submissions, official submission
authority, batch execution, retry-chain authority, unbounded command
execution, target mutation outside a released local sandbox/write scope,
runtime transition, product authorization, graph-memory authority, recursive
policy amendment, PR creation, commit, merge, release, or future-family
selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v84.md`, which selected the
`PB-MATRIX-INCLUSION-0` ProgramBench local cleanroom matrix-inclusion family.
`vNext+266`, `vNext+267`, and `vNext+268` then closed
`PB-MATRIX-INCLUSION-0-A`, `PB-MATRIX-INCLUSION-0-B`, and
`PB-MATRIX-INCLUSION-0-C` without creating additional family selector
versions.

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
- `PB-MATRIX-INCLUSION-0` is closed on `main` as local cleanroom matrix
  membership revision governance.
- latest closed implementation arc: `vNext+268`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v84.md`
- next planning obligation: select a post-`PB-MATRIX-INCLUSION-0` family
  that can run one local cleanroom specimen without converting the specimen
  into official ProgramBench participation, benchmark scoring, baseline
  comparison, model ranking, hidden-test inference, or batch execution.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

## Next Planning Question

Now that the repo can govern local case supply, local matrices, and matrix
membership revision, should the next practical family govern one bounded
local cleanroom run against one selected ProgramBench-style case, without
claiming benchmark truth or official ProgramBench standing?

The candidate:

```text
PB-SINGLE-CASE-RUN-0:
  ProgramBench Local Cleanroom Single Case Run
```

This selector treats `PB-SINGLE-CASE-RUN-0` as a one-specimen local execution
family. It is not an official ProgramBench runner, solver, evaluator
integration, submission path, hidden-test interface, benchmark score lane,
baseline comparison lane, leaderboard lane, model-ranking lane, batch runner,
or retry-chain lane.

It is also not a replacement for `PB-TRIAL-0`. It is a selected
matrix/case-lineage run wrapper that binds one released case lineage to the
already-established adapter, workbench, attempt, trial, and retry evidence
vocabulary.

Controlling invariant:

```text
PB-SINGLE-CASE-RUN-0 may run exactly one local cleanroom specimen under
released local case, workbench, attempt, trial, and sandbox law.

It may not treat that specimen as official ProgramBench evaluation,
hidden-test equivalence, benchmark score, baseline comparison, model ranking,
or proof of general benchmark performance.
```

Single-case invariant:

```text
One selected case lineage
  -> one preflighted run control packet
  -> one bounded local worker dispatch specimen
  -> one captured local probe/evidence bundle
  -> one local-only outcome audit
```

## Recommended Next Pressure

- family / practical arc: `PB-SINGLE-CASE-RUN-0`
- proposed name:
  - `PB-SINGLE-CASE-RUN-0: ProgramBench Local Cleanroom Single Case Run`
- recommended planning posture:
  - select `PB-SINGLE-CASE-RUN-0` as the next practical family after
    `PB-MATRIX-INCLUSION-0`;
  - select `PB-SINGLE-CASE-RUN-0-A` as the next default candidate after this
    family bundle is reviewed;
  - consume released `PB-ADAPTER-0`, `PB-RECON-0`, `PB-ATTEMPT-0`,
    `PB-TRIAL-0`, optional `PB-RETRY-0`, `PB-MATRIX-0`,
    `PB-CASE-EXPANSION-0`, and `PB-MATRIX-INCLUSION-0` rows as constraints,
    not new authority;
  - default target selection to a released `PB-MATRIX-INCLUSION-0-C`
    included matrix member;
  - allow direct ready expanded-case lineage or direct adapter-case intake
    only with explicit route posture and warning rows;
  - start with target selection, run request, local execution preflight,
    run control contract, and non-authority guardrail;
  - defer actual worker dispatch, execution capture, probe observation,
    candidate artifact capture, and lifecycle projection to
    `PB-SINGLE-CASE-RUN-0-B`;
  - defer local outcome audit, observation summary, remand/acceptance
    decision, handoff, and family closeout to `PB-SINGLE-CASE-RUN-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-SINGLE-CASE-RUN-0-A` | Single-case run request, target selection, execution preflight, run control contract, and non-authority guardrail |
| `PB-SINGLE-CASE-RUN-0-B` | One local worker dispatch specimen, execution capture, probe observation bundle, candidate artifact capture, and lifecycle projection |
| `PB-SINGLE-CASE-RUN-0-C` | Local outcome audit, observation summary, remand/acceptance decision, pressure-only handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-SINGLE-CASE-RUN-0-A` should be the first active slice. Candidate starter
surfaces:

- `programbench_single_case_run_request@1`
- `programbench_single_case_target_selection@1`
- `programbench_single_case_execution_preflight@1`
- `programbench_single_case_run_control_contract@1`
- `programbench_single_case_run_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` while the family remains ProgramBench-shaped
  local cleanroom execution substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_single_case_run.py`;
- defer generic benchmark-suite, official-evaluator, leaderboard,
  batch-runner, baseline-comparison, or model-ranking splits to later
  families only if explicitly selected.

Avoid names such as `programbench_runner`, `programbench_eval`,
`programbench_solver`, `programbench_submitter`, `programbench_scoreboard`,
`programbench_leaderboard`, `programbench_batch_runner`,
`programbench_baseline_scorer`, and `programbench_official_run`; those imply
official benchmark, solving, evaluation, submission, ranking, batch
execution, or score authority that this family does not select.

## `PB-SINGLE-CASE-RUN-0-A` Output Contract

`PB-SINGLE-CASE-RUN-0-A` should output only:

1. `programbench_single_case_run_request@1`
2. `programbench_single_case_target_selection@1`
3. `programbench_single_case_execution_preflight@1`
4. `programbench_single_case_run_control_contract@1`
5. `programbench_single_case_run_non_authority_guardrail@1`
6. deferred handoff notes for `PB-SINGLE-CASE-RUN-0-B` and
   `PB-SINGLE-CASE-RUN-0-C`

It should not output:

- worker dispatch records;
- local execution traces;
- probe observation bundles;
- candidate artifact captures;
- lifecycle projections;
- local outcome audits;
- remand decisions;
- benchmark scores;
- baseline comparison rows;
- model ranking rows;
- official ProgramBench participation rows;
- generated official submissions;
- batch execution rows;
- retry-chain authority;
- future-family selection.

## Review-Hardened Requirements

The family review should focus on the action-adjacent boundary:

- A may mark a specimen eligible for later local execution review, but cannot
  dispatch a worker.
- B may execute at most one local specimen and must bind execution to the A
  run control packet, sandbox witness requirements, and released local case
  lineage.
- C may audit local-only observations and emit remand/acceptance posture, but
  cannot claim official benchmark truth, baseline-relative performance, model
  ranking, or hidden-test equivalence.

The first execution specimen must bind:

- selected case lineage ref and hash;
- worker-visible input packet hash;
- runbook hash;
- sandbox policy hash;
- tool manifest hash;
- allowed write-scope hash;
- local probe basis hash;
- output capture hashes;
- candidate artifact manifest hash;
- lifecycle projection hash.

Validator expectation:

```text
No local execution row is valid unless it resolves to exactly one released
PB-SINGLE-CASE-RUN-0-A preflight packet and one selected case lineage.
```

Target-origin expectation:

```text
target_origin_route = matrix_member is the default.

If target_origin_route = ready_expanded_case_lineage, the selected case must
carry released readiness and no contamination blockers.

If target_origin_route = direct_adapter_case_exception, explicit exception
posture and a non-matrix-lineage warning are required.
```

## Deferred Families

The following are not selected by this draft:

- official ProgramBench participation governance;
- official runner/evaluator integration;
- hidden evaluator result governance;
- benchmark scoring / baseline comparison governance;
- model comparison / model-ranking governance;
- batch execution over a matrix;
- multi-case result projection;
- retry-chain or second-retry expansion;
- external source lookup / decompilation / internet evidence governance;
- generated official submission review.

## Selection Recommendation

Select `PB-SINGLE-CASE-RUN-0` as the next family, with
`PB-SINGLE-CASE-RUN-0-A` as the next active slice after review.

Recommended family decision:

```text
SELECT_PB_SINGLE_CASE_RUN_0_LOCAL_CLEANROOM_ONE_SPECIMEN_RUN_GOVERNANCE
```

Recommended first-slice decision after review:

```text
SELECT_PB_SINGLE_CASE_RUN_0A_RUN_REQUEST_TARGET_SELECTION_AND_PREFLIGHT_ONLY
```

Post-`PB-SINGLE-CASE-RUN-0-A` continuation posture: after
`PB-SINGLE-CASE-RUN-0-A` closes on `main`, select `PB-SINGLE-CASE-RUN-0-B` as the next default candidate for the next canonical starter bundle.
`PB-SINGLE-CASE-RUN-0-B` remains bounded to one local execution specimen
capture under released A controls and does not authorize outcome audit,
acceptance/remand, retry authority, batch execution, benchmark scoring,
baseline comparison, model ranking, official participation, or future-family
selection.
