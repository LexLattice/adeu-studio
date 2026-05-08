# Draft Next Arc Options v79

Status: planning handoff after `vNext+250` / `PB-RECON-0-C` merged on
`main` and after the `PB-RECON-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-RECON-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, unbounded command execution, target
mutation outside an explicit later local sandbox, runtime transition, product
authorization, graph-memory authority, recursive policy amendment, PR
creation, commit, merge, release, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v78.md`, which selected the `PB-RECON-0`
ProgramBench cleanroom reconstruction workbench family. `vNext+248`,
`vNext+249`, and `vNext+250` then closed `PB-RECON-0-A`, `PB-RECON-0-B`, and
`PB-RECON-0-C` without creating additional family selector versions.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `PB-PY-0` is closed on `main` as a local ProgramBench-shaped Python
  reconstruction realization research family.
- `PB-ADAPTER-0` is closed on `main` as a ProgramBench cleanroom adapter
  membrane family.
- `PB-RECON-0` is closed on `main` as a local cleanroom reconstruction
  workbench family.
- latest closed implementation arc: `vNext+250`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v78.md`
- next planning obligation: select a post-`PB-RECON-0` family without
  converting local workbench readiness, local remand posture, or local probe
  records into official benchmark participation, hidden-test inference,
  benchmark scoring, model ranking, or official submission authority.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `PB-RECON-0` can represent a ready cleanroom case packet as a
work order, worker-visible context, sandbox/budget law, local evidence
capture, local audit, result summary, and handoff pressure, should the next
practical family make a single local reconstruction worker attempt lifecycle
reviewable under that workbench boundary?

The candidate:

```text
PB-ATTEMPT-0:
  ProgramBench Cleanroom Reconstruction Attempt Harness
```

This selector treats `PB-ATTEMPT-0` as a local cleanroom worker-attempt family.
It is not an official ProgramBench runner, solver, evaluator integration,
submission path, hidden-test interface, benchmark score lane, or model-ranking
lane.

Controlling invariant:

```text
PB-ATTEMPT-0 may make a local cleanroom reconstruction attempt lifecycle
reviewable under released PB-RECON-0 workbench rows, but it may not turn a
worker attempt, candidate artifact, local probe result, remand, or local
acceptance into official ProgramBench participation, benchmark truth,
official submission authority, model ranking, or future-family selection.
```

Operational cleanroom invariant:

```text
The harness owns attempt eligibility, worker input assembly, sandbox preflight,
candidate materialization boundaries, local evidence export, and remand
routing. The worker may produce candidate material only inside the released
local workbench boundary and may not see hidden, forbidden, postmortem-only,
or excluded-derived evidence.
```

## Recommended Next Pressure

- family / practical arc: `PB-ATTEMPT-0`
- proposed name:
  - `PB-ATTEMPT-0: ProgramBench Cleanroom Reconstruction Attempt Harness`
- recommended planning posture:
  - select `PB-ATTEMPT-0` as the next practical family after `PB-RECON-0`;
  - select `PB-ATTEMPT-0-A` as the next default candidate for `vNext+251`
    after this family bundle is reviewed;
  - consume released `PB-RECON-0` work order, worker context, exclusion
    manifest, sandbox policy, run budget, local evidence rows, local audit
    rows, result summary, handoff, and family closeout alignment;
  - consume released `PB-ADAPTER-0` case-packet and visibility/access law as
    substrate;
  - consume released `PB-PY-0` concept/profile/Python realization rows as
    advisory reconstruction substrate;
  - start with attempt request, worker input packet, dispatch preflight, and
    non-authority guardrail;
  - defer worker invocation/output capture and candidate materialization to
    `PB-ATTEMPT-0-B`;
  - defer workbench evidence export, attempt result review, remand queue, and
    family closeout alignment to `PB-ATTEMPT-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-ATTEMPT-0-A` | Attempt request, worker input packet, dispatch eligibility/preflight, and attempt non-authority guardrail |
| `PB-ATTEMPT-0-B` | Worker invocation record, output capture, candidate materialization record, and sandbox application trace |
| `PB-ATTEMPT-0-C` | Workbench evidence export, attempt result review, remand queue, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-ATTEMPT-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom attempt substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`;
- defer any generic orchestration split to a later family only if the attempt
  harness widens beyond ProgramBench-shaped cleanroom reconstruction.

Avoid names such as `programbench_runner`, `programbench_solver`,
`programbench_eval`, `programbench_submitter`, and
`programbench_scoreboard`; those imply official benchmark, solving,
evaluation, submission, or ranking authority that this family does not select.

## `PB-ATTEMPT-0-A` Output Contract

`PB-ATTEMPT-0-A` should output only:

1. `programbench_reconstruction_attempt_request@1`
2. `programbench_reconstruction_attempt_worker_input_packet@1`
3. `programbench_reconstruction_attempt_dispatch_preflight@1`
4. `programbench_reconstruction_attempt_non_authority_guardrail@1`
5. deferred handoff notes for `PB-ATTEMPT-0-B` and `PB-ATTEMPT-0-C`

`PB-ATTEMPT-0-A` must make the attempt boundary stable enough to answer:

```text
is this released local cleanroom workbench row set eligible to package as a
bounded worker-attempt input, and what exact worker-visible material would be
provided if a later slice authorized the local attempt?
```

Worker-input exclusion summaries are especially sensitive. They may record
only exclusion category, count, reason code, authority posture, and a
non-exposure statement. They must not include source paths, source names,
content excerpts, semantic summaries, derived facts, test names, hidden
artifact identifiers, original-source clues, or other content-bearing fields.

`PB-ATTEMPT-0-A` should also make these packet/preflight facts explicit:

- `worker_input_manifest_hash`
- `worker_visible_ref_count`
- `forbidden_ref_exposure_check_hash`
- `preflight_scope_posture = eligibility_review_only_no_invocation`

Attempt requests must consume a compatible `PB-RECON-0` result-summary
posture. Remand-targeted or evidence-gap attempts may consume
`local_remand_required`, `inconclusive_local_audit`, or
`blocked_by_missing_evidence` with explicit justification. `local_accepted`,
`blocked_by_contamination`, `blocked_by_sandbox_violation`, and
`future_family_only` result summaries must not become attempt requests unless
a later lock adds a narrower rule.

It should not output:

- worker invocation transcripts;
- worker-generated candidate files;
- candidate materialization records;
- local command execution traces;
- local probe result logs;
- workbench evidence exports;
- attempt result reviews;
- remand queue entries;
- official ProgramBench submissions;
- benchmark scores;
- model rankings;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- future-family selection.

## Non-Selected Arcs

This selector maps but does not select:

- official ProgramBench participation;
- benchmark-result governance;
- hidden evaluator result governance;
- model-ranking or leaderboard surfaces;
- generated official submission review;
- larger local fixture matrix expansion;
- generalized multi-language realization overlays;
- full conceptual-first retrieval broker implementation;
- natural task-to-program-profile inference outside a released cleanroom case
  packet;
- reconstruction execution outside a local cleanroom sandbox;
- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack review;
- `V88` deterministic closeout transition / remand routing;
- canonical implementation-lock review;
- product authority, graph-memory authority, release authority, or recursive
  policy amendment.

## Decision

Select `PB-ATTEMPT-0` as the next family-level planning candidate. The first
slice should be `PB-ATTEMPT-0-A`, but the `vNext+251` lock, stop-gate
decision, and edge assessment are intentionally left for the later per-slice
starter bundle after this family bundle is reviewed.

Post-`PB-ATTEMPT-0-A` continuation posture: after `vNext+251` closes on
`main`, select `PB-ATTEMPT-0-B` as the next default candidate for the next
canonical starter bundle. That selection remains inside the already selected
`PB-ATTEMPT-0` family and does not create a new next-arc-options selector
version.

Post-`PB-ATTEMPT-0-B` continuation posture: after `PB-ATTEMPT-0-B` closes on
`main`, select `PB-ATTEMPT-0-C` as the next default candidate for the next
canonical starter bundle. That selection remains inside the already selected
`PB-ATTEMPT-0` family.
