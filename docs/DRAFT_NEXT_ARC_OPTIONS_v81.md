# Draft Next Arc Options v81

Status: planning handoff after `vNext+256` / `PB-TRIAL-0-C` merged on
`main` and after the `PB-TRIAL-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-TRIAL-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
retry dispatch authority, multi-attempt comparison, unbounded command
execution, target mutation outside a released local sandbox/write scope,
runtime transition, product authorization, graph-memory authority, recursive
policy amendment, PR creation, commit, merge, release, or future-family
selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v80.md`, which selected the `PB-TRIAL-0`
ProgramBench local cleanroom reconstruction trial family. `vNext+254`,
`vNext+255`, and `vNext+256` then closed `PB-TRIAL-0-A`, `PB-TRIAL-0-B`,
and `PB-TRIAL-0-C` without creating additional family selector versions.

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
- latest closed implementation arc: `vNext+256`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v80.md`
- next planning obligation: select a post-`PB-TRIAL-0` family without
  converting local remand pressure, local acceptance, trial observation,
  candidate artifacts, or runbook satisfaction into retry dispatch authority,
  multi-attempt comparison, benchmark truth, model ranking, or official
  ProgramBench participation.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `PB-TRIAL-0` can docket one local trial, run it as a bounded local
specimen, capture execution, snapshot a candidate, project lifecycle evidence,
audit the local outcome, and emit local-only remand pressure, should the next
practical family govern how remand pressure may become a bounded retry
candidate?

The candidate:

```text
PB-RETRY-0:
  ProgramBench Local Cleanroom Trial Retry Governance
```

This selector treats `PB-RETRY-0` as a local retry-governance family over a
released `PB-TRIAL-0` remand decision and trial lineage. It is not an
official ProgramBench runner, solver, evaluator integration, submission path,
hidden-test interface, benchmark score lane, model-ranking lane,
multi-attempt comparison lane, or unbounded retry framework.

Controlling invariant:

```text
PB-RETRY-0 may make a local remand-to-retry lifecycle reviewable for one
trial lineage, but it may not turn remand pressure, retry eligibility,
retry execution, retry outcome, or retry delta observations into official
ProgramBench participation, benchmark truth, hidden-test equivalence,
model ranking, official submission authority, unbounded retry authority, or
future-family selection.
```

Operational retry invariant:

```text
Remand pressure is not retry dispatch authority. A retry candidate must first
prove released trial lineage, local-only remand source, cleanroom continuity,
bounded scope, unchanged forbidden-evidence posture, and explicit later
dispatch authority before any retry execution-shaped row can validate.
```

Retry-loop invariant:

```text
For a given trial_lineage_ref + trial_remand_decision_ref, PB-RETRY-0 may
make at most one retry request eligible. Multiple "single retry" requests over
the same remand are retry-loop laundering unless a later family grants
retry-chain authority.
```

## Recommended Next Pressure

- family / practical arc: `PB-RETRY-0`
- proposed name:
  - `PB-RETRY-0: ProgramBench Local Cleanroom Trial Retry Governance`
- recommended planning posture:
  - select `PB-RETRY-0` as the next practical family after `PB-TRIAL-0`;
  - select `PB-RETRY-0-A` as the next default candidate for `vNext+257`
    after this family bundle is reviewed;
  - consume released `PB-TRIAL-0` outcome audit, observation summary, remand
    decision, trial family closeout alignment, and the released trial A/B
    lineage that those rows validate;
  - consume released `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and
    `PB-PY-0` closeout lineage as constraints, not new authority;
  - start with retry request intake, remand source index, retry eligibility
    review, retry scope contract, and retry non-authority guardrail;
  - defer any retry dispatch, execution capture, retry candidate delta
    snapshot, or retry lifecycle projection to `PB-RETRY-0-B`;
  - defer retry outcome audit, retry delta observation summary, remand
    settlement, and family closeout alignment to `PB-RETRY-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-RETRY-0-A` | Retry request intake, remand source index, retry eligibility review, retry scope contract, and retry non-authority guardrail |
| `PB-RETRY-0-B` | Local retry dispatch specimen, retry execution capture, retry candidate delta snapshot, retry lifecycle projection, and sandbox application trace |
| `PB-RETRY-0-C` | Retry outcome audit, same-lineage retry delta observation summary, remand settlement decision, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-RETRY-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_local_retry_request@1`
- `programbench_local_retry_lineage_registry@1`
- `programbench_trial_remand_source_index@1`
- `programbench_local_retry_eligibility_review@1`
- `programbench_local_retry_scope_contract@1`
- `programbench_local_retry_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom retry-governance substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`;
- defer any generic retry orchestration split to a later family only if the
  retry harness widens beyond ProgramBench-shaped local reconstruction.

Avoid names such as `programbench_runner`, `programbench_solver`,
`programbench_eval`, `programbench_submitter`, `programbench_scoreboard`, and
`programbench_retry_runner`; those imply official benchmark, solving,
evaluation, submission, ranking, or execution authority that this family does
not select.

## `PB-RETRY-0-A` Output Contract

`PB-RETRY-0-A` should output only:

1. `programbench_local_retry_request@1`
2. `programbench_local_retry_lineage_registry@1`
3. `programbench_trial_remand_source_index@1`
4. `programbench_local_retry_eligibility_review@1`
5. `programbench_local_retry_scope_contract@1`
6. `programbench_local_retry_non_authority_guardrail@1`
7. deferred handoff notes for `PB-RETRY-0-B` and `PB-RETRY-0-C`

`PB-RETRY-0-A` must make the retry boundary stable enough to answer:

```text
is this released PB-TRIAL-0 remand decision eligible to become one bounded
local cleanroom retry candidate, and what exact scope, unchanged evidence
boundary, retry depth, and non-authority guardrails would govern it if a
later slice ran it?
```

It should not output:

- retry dispatch records;
- retry worker transcripts;
- generated retry candidate files;
- retry candidate delta snapshots;
- local retry execution capture;
- local retry probe results;
- retry lifecycle projection rows;
- retry outcome audit;
- retry delta observation summary;
- remand settlement rows;
- second retry or retry-chain authority;
- official ProgramBench submissions;
- benchmark scores;
- model rankings;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- future-family selection.

`PB-RETRY-0-A` may consume released `PB-TRIAL-0` remand decision rows only as
local remand source and retry-eligibility substrate. Those rows must not be
treated as retry dispatch authority, evidence of a retry outcome, or
permission to widen the worker-visible context. A retry outcome can appear
only after the later `PB-RETRY-0-B` execution specimen and `PB-RETRY-0-C`
outcome audit exist.

The A starter should make these additional readiness facts explicit:

- `retry_lineage_ref`
- `source_remand_decision_ref`
- `retry_lineage_registry_ref`
- `prior_retry_request_refs`
- `retry_sequence_index`
- `retry_uniqueness_posture`
- `retry_depth_limit`
- `retry_scope_delta_refs`
- `retry_scope_delta_manifest_hash`
- `unchanged_cleanroom_boundary_refs`
- `unchanged_worker_visible_source_set_hash`
- `unchanged_forbidden_source_set_hash`
- `unchanged_tool_policy_hash`
- `unchanged_sandbox_policy_hash`
- `unchanged_write_scope_hash`
- `unchanged_network_policy_hash`
- `retry_dispatch_authority_posture =
  no_retry_dispatch_authority_granted_by_pb_retry_0a`

`PB-RETRY-0-A` should reject a retry request if the prior trial was locally
accepted, contaminated, sandbox-blocked, official-only, hidden-test-derived,
or missing a local remand decision. It should also reject many separate
retry requests that each claim `retry_depth_limit = 1` for the same released
trial remand decision.

## Non-Selected Arcs

This selector maps but does not select:

- second or unbounded retry chains;
- multi-attempt comparison;
- model-ranking or leaderboard surfaces;
- larger local cleanroom fixture matrices;
- official ProgramBench participation;
- benchmark-result governance;
- hidden evaluator result governance;
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
select PB-RETRY-0 as the next ProgramBench practical family
select PB-RETRY-0-A as the next slice candidate after review
do not select official ProgramBench participation, multi-attempt comparison,
model ranking, or unbounded retry chains
```

Post-`PB-RETRY-0-A` continuation posture: after `vNext+257` closes on
`main`, select `PB-RETRY-0-B` as the next default candidate inside the already
selected `PB-RETRY-0` family, subject to its own `vNext+258` lock, stop-gate
decision, and edge assessment.

Post-`PB-RETRY-0-B` continuation posture: after `vNext+258` closes on
`main`, select `PB-RETRY-0-C` as the next default candidate inside the already
selected `PB-RETRY-0` family, subject to its own `vNext+259` lock, stop-gate
decision, and edge assessment.
