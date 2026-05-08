# Draft Next Arc Options v78

Status: planning handoff after `vNext+247` / `PB-ADAPTER-0-C` merged on
`main` and after the `PB-ADAPTER-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-ADAPTER-0` frontier. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, arbitrary command execution outside
an explicit later local workbench lock, target mutation outside an explicit
later local sandbox, runtime transition, product authorization, graph-memory
authority, recursive policy amendment, PR creation, commit, merge, release, or
future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v77.md`, which selected the `PB-ADAPTER-0`
ProgramBench cleanroom task adapter family. `vNext+245`, `vNext+246`, and
`vNext+247` then closed `PB-ADAPTER-0-A`, `PB-ADAPTER-0-B`, and
`PB-ADAPTER-0-C` without creating additional family selector versions.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `PB-PY-0` is closed on `main` as a local ProgramBench-shaped Python
  reconstruction realization research family.
- `PB-ADAPTER-0` is closed on `main` as a ProgramBench cleanroom adapter
  membrane family.
- latest closed implementation arc: `vNext+247`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v77.md`
- next planning obligation: select a post-`PB-ADAPTER-0` family without
  converting case-packet readiness into official benchmark participation,
  hidden-test inference, benchmark scoring, model ranking, or submission
  authority.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `PB-ADAPTER-0` can represent cleanroom task-visible material,
artifact identity, visibility/access law, local/reference probe observations,
reconstruction case packets, readiness summaries, and handoff pressure, should
the next practical family build a bounded local reconstruction workbench that
can turn a ready case packet into a local reconstruction attempt and local
probe audit?

The candidate:

```text
PB-RECON-0:
  ProgramBench Cleanroom Reconstruction Workbench
```

This selector treats `PB-RECON-0` as a local cleanroom reconstruction
workbench family. It is not an official ProgramBench runner, solver,
evaluator integration, submission path, hidden-test interface, benchmark score
lane, or model-ranking lane.

Controlling invariant:

```text
PB-RECON-0 may make local cleanroom reconstruction work orders, worker context,
candidate artifacts, sandboxed local run observations, and local equivalence
audits reviewable, but it may not run official ProgramBench, expose hidden or
forbidden evidence, infer from hidden tests, generate official submissions,
claim benchmark truth, score benchmarks, or rank models.
```

Operational cleanroom invariant:

```text
The worker may see only sources authorized by the released case packet and
worker context. The harness owns sandbox policy, local run boundaries, probe
selection, artifact capture, and remand/closeout routing.
```

## Recommended Next Pressure

- family / practical arc: `PB-RECON-0`
- proposed name:
  - `PB-RECON-0: ProgramBench Cleanroom Reconstruction Workbench`
- recommended planning posture:
  - select `PB-RECON-0` as the next practical family after `PB-ADAPTER-0`;
  - select `PB-RECON-0-A` as the next default candidate for `vNext+248`
    after this family bundle is reviewed;
  - consume released `PB-ADAPTER-0` case packet, readiness, handoff, access,
    visibility, probe observation, I/O artifact, and side-effect surfaces;
  - consume released `PB-PY-0` profile and Python realization overlay
    surfaces as advisory reconstruction substrate;
- start with reconstruction work order, worker-visible context packet,
  auditor-only context exclusion manifest, sandbox policy, budget, and
  non-authority guardrail;
  - defer candidate artifact capture and local run observations to
    `PB-RECON-0-B`;
  - defer equivalence audit, result summary, handoff, and family closeout
    alignment to `PB-RECON-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-RECON-0-A` | Reconstruction work order, worker-visible context packet, auditor-only context exclusion manifest, sandbox policy, run budget, and non-authority guardrail |
| `PB-RECON-0-B` | Candidate reconstruction artifact manifest, local sandbox run trace, probe result log, and remand/correction record |
| `PB-RECON-0-C` | Local equivalence audit, reconstruction result summary, post-reconstruction handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-RECON-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains ProgramBench-shaped local
  cleanroom reconstruction substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_reconstruction.py`;
- split later only if the workbench widens into a general benchmark execution,
  official evaluation, or model-ranking platform.

Avoid names such as `programbench_runner`, `programbench_solver`,
`programbench_eval`, `programbench_submitter`, and
`programbench_scoreboard`; those imply official benchmark, solving,
evaluation, submission, or ranking authority that this family does not select.

## `PB-RECON-0-A` Output Contract

`PB-RECON-0-A` should output only:

1. `programbench_reconstruction_work_order@1`
2. `programbench_reconstruction_worker_context_packet@1`
3. `programbench_reconstruction_context_exclusion_manifest@1`
4. `programbench_reconstruction_sandbox_policy@1`
5. `programbench_reconstruction_run_budget@1`
6. `programbench_reconstruction_non_authority_guardrail@1`
7. deferred handoff notes for `PB-RECON-0-B` and `PB-RECON-0-C`

`PB-RECON-0-A` must make the worker boundary stable enough to answer:

```text
what exact case packet, visible context, local sandbox, and budget could a
later reconstruction worker use?
```

The worker context packet must contain only worker-visible refs. Hidden,
forbidden, postmortem-only, and excluded derived-summary refs belong in a
separate auditor-only exclusion manifest and must not be served into worker
context.

It should not output:

- generated Python implementation artifacts;
- candidate submission artifacts;
- local execution traces;
- probe result logs;
- remand/correction transcripts;
- equivalence audits;
- benchmark scores;
- model rankings;
- official ProgramBench task execution;
- official runner/evaluator integration;
- hidden-test handling;
- generated official submissions.

## Non-Selected Arcs

This selector maps but does not select:

- official ProgramBench participation;
- benchmark-result governance;
- full conceptual-first retrieval broker implementation;
- generalized multi-language realization overlays;
- larger fixture matrix expansion without a workbench boundary;
- hidden-test result governance;
- model-ranking or leaderboard surfaces;
- reconstruction execution outside a local cleanroom sandbox;
- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack review;
- `V88` deterministic closeout transition / remand routing;
- canonical implementation-lock review;
- product authority, graph-memory authority, release authority, or recursive
  policy amendment.

## Decision

Select `PB-RECON-0` as the next family-level planning candidate. The first
slice should be `PB-RECON-0-A`, but the `vNext+248` lock, stop-gate decision,
and edge assessment are intentionally left for the later per-slice starter
bundle after this family bundle is reviewed.

Post-`PB-RECON-0-A` continuation posture: after `vNext+248` closes on `main`,
select `PB-RECON-0-B` as the next default candidate for the next canonical
starter bundle. That selection remains inside the already selected
`PB-RECON-0` family and does not create a new next-arc-options selector
version.

Post-`PB-RECON-0-B` continuation posture: after `PB-RECON-0-B` closes on
`main`, select `PB-RECON-0-C` as the next default candidate for the next
canonical starter bundle. That selection remains inside the already selected
`PB-RECON-0` family.
