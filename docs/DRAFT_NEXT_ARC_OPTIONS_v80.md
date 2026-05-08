# Draft Next Arc Options v80

Status: planning handoff after `vNext+253` / `PB-ATTEMPT-0-C` merged on
`main` and after the `PB-ATTEMPT-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-ATTEMPT-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, retry authority, multi-attempt
comparison, unbounded command execution, target mutation outside a released
local sandbox, runtime transition, product authorization, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v79.md`, which selected the `PB-ATTEMPT-0`
ProgramBench cleanroom reconstruction attempt lifecycle family. `vNext+251`,
`vNext+252`, and `vNext+253` then closed `PB-ATTEMPT-0-A`,
`PB-ATTEMPT-0-B`, and `PB-ATTEMPT-0-C` without creating additional family
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
- latest closed implementation arc: `vNext+253`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v79.md`
- next planning obligation: select a post-`PB-ATTEMPT-0` family without
  converting local attempt lifecycle readiness, local invocation records,
  candidate artifacts, local acceptance, or remand pressure into official
  benchmark participation, hidden-test inference, benchmark scoring, model
  ranking, retry authority, or official submission authority.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `PB-ATTEMPT-0` can package a local attempt request, worker-visible
input packet, dispatch preflight, bounded invocation record, output capture,
candidate materialization, sandbox application trace, workbench evidence
export, result review, remand queue, and family closeout alignment, should
the next practical family run one local cleanroom reconstruction trial through
that lifecycle?

The candidate:

```text
PB-TRIAL-0:
  ProgramBench Local Cleanroom Reconstruction Trial
```

This selector treats `PB-TRIAL-0` as a local trial family over released
`PB-ATTEMPT-0` lifecycle law. It is not an official ProgramBench runner,
solver, evaluator integration, submission path, hidden-test interface,
benchmark score lane, model-ranking lane, retry framework, or multi-attempt
comparison lane.

Controlling invariant:

```text
PB-TRIAL-0 may instantiate and record one local cleanroom reconstruction
trial under released PB-ATTEMPT-0 lifecycle rows, but it may not turn that
trial, candidate artifact, local probe result, local acceptance, or remand
pressure into official ProgramBench participation, benchmark truth, official
submission authority, model ranking, retry authority, or future-family
selection.
```

Operational trial invariant:

```text
The harness owns trial docket selection, runbook construction, sandbox
readiness review, worker-visible packet binding, execution capture, candidate
snapshotting, lifecycle projection, local outcome audit, and closeout. The
worker may act only inside the released local cleanroom trial boundary and may
not see hidden, forbidden, postmortem-only, or excluded-derived evidence.
```

## Recommended Next Pressure

- family / practical arc: `PB-TRIAL-0`
- proposed name:
  - `PB-TRIAL-0: ProgramBench Local Cleanroom Reconstruction Trial`
- recommended planning posture:
  - select `PB-TRIAL-0` as the next practical family after `PB-ATTEMPT-0`;
  - select `PB-TRIAL-0-A` as the next default candidate for `vNext+254`
    after this family bundle is reviewed;
  - consume released `PB-ATTEMPT-0` attempt request, worker input packet,
    dispatch preflight, guardrail, invocation capture, materialization,
    evidence export, result review, remand queue, and family closeout
    alignment;
  - consume released `PB-RECON-0` workbench state, `PB-ADAPTER-0` cleanroom
    case-packet law, and `PB-PY-0` advisory realization substrate;
  - start with trial docket, execution runbook, sandbox readiness review, and
    trial non-authority guardrail;
  - defer actual local worker execution and candidate snapshotting to
    `PB-TRIAL-0-B`;
  - defer local outcome audit, observation summary, remand decision, and
    family closeout alignment to `PB-TRIAL-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-TRIAL-0-A` | Trial docket, local execution runbook, sandbox readiness review, and trial non-authority guardrail |
| `PB-TRIAL-0-B` | Local worker dispatch specimen, execution capture, candidate artifact snapshot, and lifecycle projection |
| `PB-TRIAL-0-C` | Local outcome audit, trial observation summary, remand decision, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-TRIAL-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_local_reconstruction_trial_docket@1`
- `programbench_local_trial_execution_runbook@1`
- `programbench_local_trial_sandbox_readiness_review@1`
- `programbench_local_trial_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom trial substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`;
- defer any generic execution-orchestration split to a later family only if
  the trial harness widens beyond ProgramBench-shaped local reconstruction.

Avoid names such as `programbench_runner`, `programbench_solver`,
`programbench_eval`, `programbench_submitter`, and
`programbench_scoreboard`; those imply official benchmark, solving,
evaluation, submission, or ranking authority that this family does not select.

## `PB-TRIAL-0-A` Output Contract

`PB-TRIAL-0-A` should output only:

1. `programbench_local_reconstruction_trial_docket@1`
2. `programbench_local_trial_execution_runbook@1`
3. `programbench_local_trial_sandbox_readiness_review@1`
4. `programbench_local_trial_non_authority_guardrail@1`
5. deferred handoff notes for `PB-TRIAL-0-B` and `PB-TRIAL-0-C`

`PB-TRIAL-0-A` must make the trial boundary stable enough to answer:

```text
is this released local attempt lifecycle package eligible to become one
bounded local cleanroom reconstruction trial, and what exact runbook,
sandbox-readiness requirements, worker-visible packet hashes, and non-authority
guardrails would govern it if a later slice ran it?
```

It should not output:

- worker dispatch records;
- worker transcripts;
- generated candidate files;
- candidate artifact snapshots;
- local execution capture;
- local probe results;
- lifecycle projection rows;
- local outcome audit;
- trial observation summary;
- remand decision rows;
- official ProgramBench submissions;
- benchmark scores;
- model rankings;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- retry authority;
- future-family selection.

`PB-TRIAL-0-A` may consume released `PB-ATTEMPT-0` result-review rows only as
lifecycle-shape, closeout-lineage, or eligibility context. Those rows must not
be treated as evidence of the new `PB-TRIAL-0` trial outcome. The new trial
outcome can appear only after the later `PB-TRIAL-0-B` execution specimen and
`PB-TRIAL-0-C` outcome audit exist.

The A starter should make these additional readiness facts explicit:

- `runbook_hash`
- `trial_input_materialization_policy_ref`
- `sandbox_witness_requirement_refs`

Sandbox readiness marked ready should require every readiness row to map to a
later B witness requirement, including a closed tool manifest. A readiness
review that marks ready while the tool manifest is not closed should be a
reject case.

## Non-Selected Arcs

This selector maps but does not select:

- retry dispatch authority;
- multi-attempt comparison;
- larger local cleanroom fixture matrices;
- official ProgramBench participation;
- benchmark-result governance;
- hidden evaluator result governance;
- model-ranking or leaderboard surfaces;
- generated official submission review;
- natural task-to-program-profile inference;
- broader conceptual broker implementation;
- generalized multi-language realization overlays;
- official runner/evaluator integration;
- hidden-test handling or hidden-test repair;
- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack review;
- `V88` deterministic closeout transition / remand routing;
- canonical implementation-lock review;
- product authority, graph-memory authority, release authority, or recursive
  policy amendment.

## Decision

Recommended selection:

```text
select PB-TRIAL-0 as the next ProgramBench practical family
select PB-TRIAL-0-A as the next slice candidate after review
do not select official ProgramBench participation or retry/multi-attempt work
```
