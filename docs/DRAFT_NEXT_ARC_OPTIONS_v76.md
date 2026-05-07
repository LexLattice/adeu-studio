# Draft Next Arc Options v76

Status: planning handoff after `vNext+241` / `V85-C` merged on `main`, after
the `V85` family closeout pass, after the V85 resident-model probe corpus was
preserved as repo evidence, and after the post-`V85` ProgramBench roadmap.

Authority layer: planning.

This draft records the post-`V85` frontier. It does not authorize obligation
expansion, evidence contracts, edge probe plans, reviewer taskpacks, audit
reports, deterministic closeout routing, implementation locks, work-packet
activation, code edits, command execution, tool invocation, target mutation,
runtime transition, official ProgramBench participation, source-code lookup,
internet use inside ProgramBench tasks, decompilation, benchmark truth, model
ranking, product authorization, graph-memory authority, recursive policy
amendment, PR creation, commit, merge, release, or future-family selection by
itself.

## Selector Versioning Posture

`DRAFT_NEXT_ARC_OPTIONS_v*` advances once per family-level selection. Sub-lanes
inside an already selected family advance through `vNext+<n>` starter /
implementation / closeout bundles.

The current family-level predecessor for this selector is
`DRAFT_NEXT_ARC_OPTIONS_v75.md`, which selected the `V85` semantic declaration
and canonical meta-list review family. `vNext+239`, `vNext+240`, and
`vNext+241` then closed `V85-A`, `V85-B`, and `V85-C` without creating
additional family selector versions.

## Current Frontier

- `V68` through `V85` are closed on `main`.
- `V85` closed semantic declaration and canonical meta-loop lookup review
  without obligation expansion, evidence contracts, edge probe plans, audit
  taskpacks, deterministic transition tables, implementation, runtime behavior,
  product authority, graph authority, recursive policy amendment, or `V86`
  selection.
- latest closed implementation arc: `vNext+241`
- latest family-level selector before this draft:
  `DRAFT_NEXT_ARC_OPTIONS_v75.md`
- next planning obligation: select a post-`V85` family outside closed `V85`.

Primary inputs:

- `docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_FAMILY_CLOSEOUT_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V85_v0.md`
- `docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md`
- `docs/support/ADEU Conceptual-First Retrieval Pipeline v1.md`
- `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
- `artifacts/agent_harness/meta_loop_probes/SERIES_INTERPRETATION_v0.md`

## Next Planning Question

Now that `V85` can record semantic declaration requests, source witnesses,
guardrails, canonical lookup rows, registries, obligation-family lookup rows,
pointer fixtures, summaries, handoffs, and family closeout alignment without
obligation expansion or implementation authority, should the next practical
family instantiate a tiny ProgramBench-style concept-to-code realization wedge?

The candidate:

```text
PB-PY-0:
  ProgramBench Python Reconstruction Realization Pack
```

This selector treats `PB-PY-0` as a local ProgramBench-shaped realization
review family, not official benchmark participation and not benchmark truth.

Controlling invariant:

```text
PB-PY-0 may make a small ProgramBench-style Python realization pack and one
cleanroom fixture reviewable, but it may not run official ProgramBench tasks,
use forbidden evidence, claim benchmark truth, submit results, rank models, or
authorize implementation outside its later bounded fixture.
```

Operational cleanroom invariant:

```text
Forbidden inference stores must not be registered, mounted, queried, or exposed
to the worker during the inference phase. Forbidden evidence may appear in
audit / postmortem posture only, not in live reconstruction context.
```

## Recommended Next Pressure

- family / practical arc: `PB-PY-0`
- proposed name:
  - `PB-PY-0: ProgramBench Python Reconstruction Realization Pack`
- recommended planning posture:
  - select `PB-PY-0` as the next practical family after `V85`;
  - select `PB-PY-0-A` as the next default candidate for `vNext+242`;
  - consume `V85` semantic declaration / lookup substrate as non-expanding,
    non-implementation, non-runtime review substrate;
  - consume the hardened conceptual-first retrieval support note as
    architecture / support, not implementation authority;
  - consume public ProgramBench descriptors as benchmark context only;
  - start with cleanroom profile intake, canonical program concept seed rows,
    and non-benchmark-truth / forbidden-evidence guardrails;
  - define the local cleanroom fixture contract in `PB-PY-0-A` without building
    the fixture instance;
  - defer Python realization overlay rows to `PB-PY-0-B`;
  - defer local cleanroom fixture and A/B/C comparison packet to `PB-PY-0-C`.

## Proposed Family Decomposition

| Slice | Role |
|---|---|
| `PB-PY-0-A` | ProgramBench cleanroom reconstruction profile intake, concept boundary seed, source/evidence posture, local fixture contract, and non-benchmark-truth guardrail |
| `PB-PY-0-B` | Python realization overlay: `ConceptRealizationRecord@1`, Python stdlib surfaces, implementation patterns, contraindications, failure modes, and witness templates |
| `PB-PY-0-C` | one local cleanroom fixture instance plus comparison packet for A/B/C: base ADEU, ADEU + conceptual profile, ADEU + conceptual profile + Python overlay |

## Selected Surfaces For Starter Drafting

`PB-PY-0-A` should be the first active slice. Candidate starter surfaces:

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`

Recommended first package ownership:

- `packages/adeu_benchmarking` if the slice is treated as benchmark-world
  posture / local fixture substrate;
- conservative submodule path:
  `packages/adeu_benchmarking/cleanroom_reconstruction/`;
- split later to a dedicated conceptual retrieval package only if `PB-PY-0`
  materially widens into a general broker.

Avoid starter names such as `programbench_runner`, `programbench_eval`, or
`programbench_solver`; those imply official benchmark or solving authority that
`PB-PY-0-A` does not select.

## PB-PY-0-A Output Contract

`PB-PY-0-A` should output only:

1. `programbench_cleanroom_reconstruction_profile@1`
2. `program_odeu_concept_boundary_seed@1`
3. `programbench_cleanroom_evidence_source_index@1`
4. `programbench_reconstruction_non_authority_guardrail@1`
5. `programbench_local_cleanroom_fixture_contract@1`, but no fixture instance
6. deferred handoff notes for `PB-PY-0-B` and `PB-PY-0-C`

`programbench_local_cleanroom_fixture_contract@1` should define:

```text
fixture_id
reference_executable_ref
usage_docs_ref
allowed_inference_sources
forbidden_inference_sources
worker_visible_files
worker_hidden_files
probe_allowed_commands
network_policy
source_visibility_policy
expected_submission_shape
evaluation_oracle_posture
non_benchmark_truth_posture
```

Initial `program_odeu_concept_boundary_seed@1` rows should include:

```text
program_behavior
command
subcommand
cli_flag
positional_argument
stdin_input
stdout_output
stderr_diagnostic
exit_code
config_file
environment_variable
default_value
precedence_rule
parser_error
runtime_error
generated_output_artifact
filesystem_side_effect
probe_log
```

Seed rows may remain `boundary_incomplete`; the point of `PB-PY-0-A` is to make
the O-lane inventory visible before Python realization overlay work begins.

Phase separation for `PB-PY-0-A`:

```text
inference_phase:
  cleanroom-visible evidence only

local_development_phase:
  worker-generated probes/tests allowed
  still no forbidden evidence

evaluation_phase:
  hidden tests may judge artifact
  hidden tests remain external court, not inference evidence

postmortem_phase:
  evaluation failures may inform harness research only under dev posture
  not retroactively admitted as inference evidence
```

`PB-PY-0-A` must not ship:

- `ConceptRealizationRecord@1`
- `PythonReconstructionPlan@1`
- implementation generation
- generated Python code
- official ProgramBench runner integration
- official ProgramBench task execution
- hidden-test handling
- internet / source / decompilation stores
- benchmark scoring or benchmark truth

## Later Slice Planning Handles

`PB-PY-0-B` candidate surfaces:

- `concept_realization_record@1`
- `python_reconstruction_realization_pack@1`
- `python_reconstruction_plan@1`
- `python_realization_witness_template@1`

`PB-PY-0-C` candidate surfaces:

- `programbench_local_cleanroom_fixture@1`
- `programbench_reconstruction_comparison_packet@1`
- `programbench_probe_equivalence_audit@1`
- `programbench_realization_family_closeout_alignment@1`

Post-`PB-PY-0-A` continuation posture: after `vNext+242` closes on `main`,
select `PB-PY-0-B` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `PB-PY-0` family
and does not create a new next-arc-options selector version.

Post-`PB-PY-0-B` continuation posture: after `PB-PY-0-B` closes on `main`,
select `PB-PY-0-C` as the next default candidate for the next canonical starter
bundle. That selection remains inside the already selected `PB-PY-0` family.

## Non-Selection

This selector handoff does not select:

- `V86`, `V87`, or `V88`;
- obligation expansion, evidence contracts, edge probe plans, reviewer
  taskpacks, audit reports, deterministic closeout transition tables, or
  remand routing;
- full conceptual-first retrieval broker implementation;
- official ProgramBench participation, benchmark submission, benchmark
  scoring, benchmark truth, or model ranking;
- original source lookup, internet lookup, decompilation, hidden evaluator
  tests as inference evidence, host secrets, Docker socket access, or
  task-external code repositories;
- implementation, command execution, tool invocation, target mutation,
  work-packet execution, implementation-lock creation, or runtime transition;
- product launch, product-market validation, or product authorization;
- corpus ingestion, customer-data handling, connector activation, endpoint
  access, or data transfer;
- graph-memory authority or living-memory runtime;
- PR creation, commit, merge, release, or released-truth authority;
- recursive policy amendment.

Those remain mapped future seams until their own planning and lock surfaces
select them.

## Entry And Non-Entry Criteria

`PB-PY-0` is selector-ready because:

- `V85` closed semantic declaration / lookup review substrate;
- the probe corpus shows resident models can obey closed semantic branch
  selection, uncertainty, remand, and no-unauthorized-transition laws;
- the hardened conceptual-first retrieval support pass explicitly maps
  ProgramBench cleanroom retrieval profiles and forbidden stores;
- ProgramBench's public task shape stresses cleanroom behavior ontology,
  witness probing, side effects, errors, exit codes, stdout/stderr, and
  implementation planning;
- a tiny Python realization pack can test the concept-to-code bridge without
  claiming official benchmark participation.

`PB-PY-0` must not be used if the only pressure is:

- "try ProgramBench now";
- benchmark leaderboard comparison;
- hidden-test inference;
- source retrieval or decompilation;
- broad conceptual broker implementation;
- generalized multi-language reconstruction;
- implementation work without a cleanroom profile / guardrail substrate;
- local fixture pass being treated as official benchmark result.
