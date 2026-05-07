# Draft Next Arc Options v77

Status: planning handoff after `vNext+244` / `PB-PY-0-C` merged on `main`
and after the `PB-PY-0` family closeout.

Authority layer: planning.

This draft records the post-`PB-PY-0` frontier. It does not authorize official
ProgramBench participation, official task execution, official runner
integration, hidden-test handling, hidden-test inference, original source
lookup, decompilation, internet lookup inside ProgramBench tasks, external
repository lookup, benchmark submission, benchmark scoring, benchmark truth,
model ranking, generated official submissions, implementation generation,
command execution, tool invocation, target mutation, runtime transition,
product authorization, graph-memory authority, recursive policy amendment,
PR creation, commit, merge, release, or future-family selection by itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v76.md`, which selected the `PB-PY-0` ProgramBench
Python reconstruction realization family. `vNext+242`, `vNext+243`, and
`vNext+244` then closed `PB-PY-0-A`, `PB-PY-0-B`, and `PB-PY-0-C` without
creating additional family selector versions.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `PB-PY-0` is closed on `main` as a local ProgramBench-shaped Python
  reconstruction realization research family.
- latest closed implementation arc: `vNext+244`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v76.md`
- next planning obligation: select a post-`PB-PY-0` family without converting
  the local reconstruction substrate into official benchmark participation.

Primary inputs:

- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V85_v0.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `PB-PY-0` can represent cleanroom reconstruction profiles, concept
boundary seeds, evidence source posture, non-authority guardrails, fixture
contracts, Python realization overlays, witness templates, one local fixture,
comparison packets, and local probe audits, should the next practical family
build the adapter layer that turns task-visible ProgramBench-style material
into bounded cleanroom reconstruction case packets?

The candidate:

```text
PB-ADAPTER-0:
  ProgramBench Cleanroom Task Adapter
```

This selector treats `PB-ADAPTER-0` as a cleanroom task intake and observation
adapter family. It is not an official ProgramBench runner, solver, evaluator
integration, submission path, hidden-test interface, benchmark score lane, or
model-ranking lane.

Controlling invariant:

```text
PB-ADAPTER-0 may make ProgramBench-style task-visible evidence, worker access
policy, probe observations, and reconstruction case packets reviewable, but it
may not run official ProgramBench, expose hidden or forbidden evidence, infer
from hidden tests, generate official submissions, claim benchmark truth, score
benchmarks, or rank models.
```

Operational cleanroom invariant:

```text
Forbidden inference stores must remain unreachable during inference. Hidden
tests and official evaluators may be external courts only under a later
authorized evaluation posture; they are never live inference evidence for this
family.
```

## Recommended Next Pressure

- family / practical arc: `PB-ADAPTER-0`
- proposed name:
  - `PB-ADAPTER-0: ProgramBench Cleanroom Task Adapter`
- recommended planning posture:
  - select `PB-ADAPTER-0` as the next practical family after `PB-PY-0`;
  - select `PB-ADAPTER-0-A` as the next default candidate for `vNext+245`
    after this family bundle is reviewed;
  - consume released `PB-PY-0` profile, fixture-contract, realization overlay,
    fixture, comparison, and probe-audit surfaces as local cleanroom substrate;
  - consume public ProgramBench descriptors as benchmark context only;
  - start with task intake, visibility manifests, worker access contracts, and
    adapter guardrails;
  - defer probe observation rows to `PB-ADAPTER-0-B`;
  - defer reconstruction case packets and adapter readiness summaries to
    `PB-ADAPTER-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-ADAPTER-0-A` | ProgramBench-style task intake, source visibility manifest, worker access contract, and non-authority guardrail |
| `PB-ADAPTER-0-B` | Probe plan and observation adapter for CLI/help/stdio/generated-artifact/filesystem-side-effect evidence |
| `PB-ADAPTER-0-C` | Reconstruction case packet, adapter readiness summary, post-adapter handoff, and family closeout alignment |

## Selected Surfaces For Starter Drafting

`PB-ADAPTER-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_cleanroom_task_intake@1`
- `programbench_task_artifact_manifest@1`
- `programbench_task_visibility_manifest@1`
- `programbench_adapter_worker_access_contract@1`
- `programbench_adapter_non_authority_guardrail@1`

Recommended package ownership:

- `packages/adeu_benchmarking` if the slice remains benchmark-world
  cleanroom adapter substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_adapter.py`;
- split later only if the adapter materially widens into a general benchmark
  or external evaluation platform.

Avoid names such as `programbench_runner`, `programbench_solver`,
`programbench_eval`, or `programbench_submitter`; those imply official
benchmark or solving authority that `PB-ADAPTER-0-A` does not select.

## `PB-ADAPTER-0-A` Output Contract

`PB-ADAPTER-0-A` should output only:

1. `programbench_cleanroom_task_intake@1`
2. `programbench_task_artifact_manifest@1`
3. `programbench_task_visibility_manifest@1`
4. `programbench_adapter_worker_access_contract@1`
5. `programbench_adapter_non_authority_guardrail@1`
6. deferred handoff notes for `PB-ADAPTER-0-B` and `PB-ADAPTER-0-C`

`PB-ADAPTER-0-A` must make artifact identity stable enough to answer:

```text
what exact task-visible artifact set was the worker allowed to see?
```

The task artifact manifest should include stable hash or snapshot witnesses for
the reference executable, usage docs, visible input artifacts, and source-set
identity. Visibility rows must distinguish known-visible, known-hidden,
known-forbidden, support-only, unknown-not-indexed, and declared-absent stores.
Hidden or forbidden rows must not be converted into cleanroom-visible derived
summaries for worker inference.

It should not output:

- probe execution records;
- CLI observation logs;
- stdio observation logs;
- generated artifact observations;
- filesystem side-effect observations;
- reconstruction case packets;
- readiness summaries;
- official ProgramBench task execution;
- official runner integration;
- hidden-test handling;
- benchmark scores;
- model rankings;
- generated official submissions.

## Non-Selected Arcs

This selector maps but does not select:

- official ProgramBench participation;
- benchmark-result governance;
- full conceptual-first retrieval broker implementation;
- generalized multi-language realization overlays;
- larger fixture matrix expansion without adapter intake law;
- natural task to program-profile inference without task-visible evidence
  manifests;
- `V86` obligation expansion / evidence contract / edge probe plan review;
- `V87` reviewer / auditor taskpack review;
- `V88` deterministic closeout transition / remand routing;
- canonical implementation-lock review;
- product authority, graph-memory authority, release authority, or recursive
  policy amendment.

## Decision

Select `PB-ADAPTER-0` as the next family-level planning candidate. The first
slice should be `PB-ADAPTER-0-A`, but the `vNext+245` lock, stop-gate decision,
and edge assessment are intentionally left for the later per-slice starter
bundle after this family bundle is reviewed.
